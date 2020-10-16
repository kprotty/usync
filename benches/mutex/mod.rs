// Copyright (c) 2020 kprotty
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{
    convert::TryInto,
    fmt,
    ops::Div,
    sync::{
        atomic::{spin_loop_hint, AtomicBool, Ordering},
        Arc, Barrier,
    },
    time::{Duration, Instant},
};

mod util;

mod futex_lock;
mod keyed_lock;
mod os_lock;
mod parking_lot_lock;
mod plot_lock;
mod simple_mutex_lock;
mod spin_lock;
mod sym_lock;
mod word_lock;
mod word_lock_fair;
mod word_lock_waking;
mod usync_lock;

fn bench_all(b: &mut Benchmarker) {
    // b.bench::<spin_lock::Lock>();
    
    b.bench::<usync_lock::Lock>();
    b.bench::<word_lock_waking::Lock>();

    b.bench::<os_lock::Lock>();
    // b.bench::<simple_mutex_lock::Lock>();
    b.bench::<parking_lot_lock::Lock>();
    b.bench::<sym_lock::Lock>();

    // b.bench::<plot_lock::Lock>();
    // b.bench::<word_lock::Lock>();
    // b.bench::<word_lock_fair::Lock>();
    

    // b.bench::<keyed_lock::Lock>();

    // b.bench::<futex_lock::FutexLock<futex_lock::OsFutex>>();
    // #[cfg(any(windows, target_os = "linux"))]
    // b.bench::<futex_lock::FutexLock<futex_lock::generic::Futex>>();
}

pub unsafe trait Lock: Send + Sync + 'static {
    const NAME: &'static str;

    fn new() -> Self;

    fn with(&self, f: impl FnOnce());
}

struct ArgParser;
impl ArgParser {
    fn parse() -> (Vec<Duration>, Vec<usize>, Vec<WorkUnit>, Vec<WorkUnit>) {
        let mut args = std::env::args().peekable();
        let _exe = args.next().unwrap();
        if args.peek().is_none() {
            Self::error("no arguments supplied");
        }

        let measure = Self::parse_item(args.next(), |results, (value, mult), second| {
            if second.is_some() {
                ArgParser::error("measure time doesn't support ranges");
            }
            let mult = mult.unwrap_or_else(|| ArgParser::error("measure requires time unit"));
            results.push(Duration::from_nanos(value * mult));
        });

        let threads = Self::parse_item(args.next(), |results, first, second| {
            if first.1.is_some() {
                ArgParser::error("threads take usize, not time unit");
            }
            let first = first
                .0
                .try_into()
                .unwrap_or_else(|_| ArgParser::error("threads take in a usize"));
            if let Some((second, mult)) = second {
                if mult.is_some() {
                    ArgParser::error("threads take usize, not time unit");
                }
                let second = second
                    .try_into()
                    .unwrap_or_else(|_| ArgParser::error("threads take in a usize"));
                if second < first {
                    ArgParser::error("invalid range of threads");
                }
                for threads in first..=second {
                    results.push(threads);
                }
            } else {
                results.push(first);
            }
        });

        fn parse_work_unit(
            results: &mut Vec<WorkUnit>,
            first: (u64, Option<u64>),
            second: Option<(u64, Option<u64>)>,
        ) {
            let first = match first {
                (_value, None) => ArgParser::error("time unit required"),
                (value, Some(mult)) => Duration::from_nanos(value * mult),
            };

            let second = second.map(|second| match second {
                (_value, None) => ArgParser::error("time unit required"),
                (value, Some(mult)) => {
                    let second = Duration::from_nanos(value * mult);
                    if second.as_nanos() < first.as_nanos() {
                        ArgParser::error("invalid time range");
                    }
                    second
                }
            });

            results.push(WorkUnit {
                from: first,
                to: second,
            });
        }

        let locked = Self::parse_item(args.next(), parse_work_unit);
        let unlocked = Self::parse_item(args.next(), parse_work_unit);

        (measure, threads, locked, unlocked)
    }

    fn parse_item<T>(
        input: Option<String>,
        mut resolve: impl FnMut(&mut Vec<T>, (u64, Option<u64>), Option<(u64, Option<u64>)>),
    ) -> Vec<T> {
        let input = input.unwrap_or_else(|| Self::error("invalid argument"));
        let mut input = input.as_bytes().iter().peekable();
        let mut results = Vec::new();

        while input.len() > 0 {
            let first = Self::parse_value(&mut input);
            let mut second = None;
            if let Some(b'-') = input.next() {
                second = Some(Self::parse_value(&mut input));
            }
            resolve(&mut results, first, second);
            match input.next() {
                None => break,
                Some(b',') => continue,
                _ => Self::error("invalid continuation"),
            }
        }

        results
    }

    fn parse_value(
        input: &mut std::iter::Peekable<std::slice::Iter<'_, u8>>,
    ) -> (u64, Option<u64>) {
        let mut value = None;
        while let Some(&c) = input.peek() {
            if *c < b'0' || *c > b'9' {
                break;
            }
            let c = input.next().unwrap();
            if let Some(v) = value {
                value = Some((v * 10) + ((c - b'0') as u64));
            } else {
                value = Some((c - b'0') as u64);
            }
        }
        let value = value.unwrap_or_else(|| Self::error("invalid value"));

        let mult = input
            .peek()
            .and_then(|c| match *c {
                b'n' => Some(1),
                b'u' => Some(1_000),
                b'm' => Some(1_000_000),
                b's' => Some(1_000_000_000),
                _ => None,
            })
            .map(|m| {
                let _ = input.next();
                if m != 1_000_000_000 {
                    match input.next() {
                        Some(b's') => {}
                        _ => Self::error("invalid time unit"),
                    }
                }
                m
            });

        (value, mult)
    }

    fn error(message: &str) -> ! {
        eprintln!("Error: {:?}\n", message);
        Self::print_help(std::env::args().next().unwrap());
        std::process::exit(1)
    }

    fn print_help(exe: String) {
        println!("Usage: {} [measure] [threads] [locked] [unlocked]", exe);
        println!("where:");

        println!();
        println!(" [measure]: [csv-ranged:time]\t\\\\ List of time spent measuring for each mutex benchmark");
        println!(" [threads]: [csv-ranged:count]\t\\\\ List of thread counts for each benchmark");
        println!(" [locked]: [csv-ranged:time]\t\\\\ List of time spent inside the lock for each benchmark");
        println!(" [unlocked]: [csv-ranged:time]\t\\\\ List of time spent outside the lock for each benchmark");

        println!();
        println!(" [count]: {{usize}}");
        println!(" [time]: {{u64}}[time_unit]");
        println!(" [time_unit]: \"ns\" | \"us\" | \"ms\" | \"s\"");

        println!();
        println!(" [csv_ranged:{{rule}}]: {{rule}}");
        println!("   | {{rule}} \"-\" {{rule}} \t\t\t\t\t\\\\ randomized value in range");
        println!(
            "   | [csv_ranged:{{rule}}] \",\" [csv_ranged:{{rule}}] \t\\\\ multiple permutations"
        );
        println!();
    }
}

#[derive(Copy, Clone)]
struct WorkUnit {
    from: Duration,
    to: Option<Duration>,
}

impl fmt::Debug for WorkUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(to) = self.to {
            write!(f, "rand({:?}, {:?})", self.from, to)
        } else {
            write!(f, "{:?}", self.from)
        }
    }
}

impl WorkUnit {
    fn scaled(self, nanos: u64) -> Self {
        let from: u64 = self.from.as_nanos().try_into().unwrap();
        Self {
            from: Duration::from_nanos(from / nanos),
            to: self.to.map(|to| {
                let to: u64 = to.as_nanos().try_into().unwrap();
                Duration::from_nanos(to / nanos)
            }),
        }
    }

    fn nanos_per_work() -> u64 {
        fn record(f: impl FnOnce()) -> Duration {
            let started = Instant::now();
            f();
            started.elapsed()
        }

        let compute = || -> u64 {
            let timer_overhead = record(|| {
                let _ = Instant::now();
            });

            let num_works = 10_000;
            let work_overhead = record(|| {
                (0..num_works).for_each(|_| Self::work());
            });

            let elapsed = (work_overhead - timer_overhead).as_nanos();
            (elapsed / num_works).max(1).try_into().unwrap()
        };

        let attempts = 10;
        (0..attempts)
            .map(|_| compute())
            .fold(0, |acc, x| acc + x)
            .div(attempts)
    }

    fn count(self, prng: &mut u64) -> u64 {
        let min: u64 = self.from.as_nanos().try_into().unwrap();
        if let Some(to) = self.to {
            let max: u64 = to.as_nanos().try_into().unwrap();
            let rng = {
                let mut x = *prng;
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                *prng = x;
                x
            };
            (rng % (max - min + 1)) + min
        } else {
            min
        }
    }

    fn work() {
        spin_loop_hint();
    }
}

#[derive(Default)]
struct BenchmarkResult {
    name: Option<&'static str>,
    mean: Option<f64>,
    stdev: Option<f64>,
    min: Option<f64>,
    max: Option<f64>,
    sum: Option<f64>,
}

impl BenchmarkResult {
    fn lower(value: f64) -> String {
        if value <= 1_000f64 {
            format!("{}", value.round())
        } else if value <= 1_000_000f64 {
            format!("{}k", (value / 1_000f64).round())
        } else if value <= 1_000_000_000f64 {
            format!("{:.2}m", value / 1_000_000f64)
        } else {
            format!("{:.2}b", value / 1_000_000_000f64)
        }
    }
}

impl fmt::Debug for BenchmarkResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:<18} |", self.name.unwrap_or("name"))?;
        write!(
            f,
            " {:>7} |",
            self.mean.map(Self::lower).unwrap_or("mean".to_string())
        )?;
        write!(
            f,
            " {:>7} |",
            self.stdev.map(Self::lower).unwrap_or("stdev".to_string())
        )?;
        write!(
            f,
            " {:>7} |",
            self.min.map(Self::lower).unwrap_or("min".to_string())
        )?;
        write!(
            f,
            " {:>7} |",
            self.max.map(Self::lower).unwrap_or("max".to_string())
        )?;
        write!(
            f,
            " {:>7} |",
            self.sum.map(Self::lower).unwrap_or("sum".to_string())
        )?;
        Ok(())
    }
}

#[derive(Copy, Clone)]
struct Benchmarker {
    measure: Duration,
    threads: usize,
    locked: WorkUnit,
    unlocked: WorkUnit,
}

impl Benchmarker {
    fn bench<L: Lock>(&self) {
        #[repr(align(512))]
        struct CacheAlign<T>(T);
        struct Context<L> {
            lock: CacheAlign<L>,
            running: AtomicBool,
            barrier: Barrier,
            this: Benchmarker,
        }

        let context = Arc::new(Context {
            lock: CacheAlign(L::new()),
            running: AtomicBool::new(true),
            barrier: Barrier::new(self.threads + 1),
            this: self.clone(),
        });

        let threads = (0..self.threads)
            .map(|_| {
                let context = context.clone();
                std::thread::spawn(move || {
                    let mut iterations = 0u64;
                    let mut prng = (&iterations as *const _ as usize).wrapping_mul(31) as u64;

                    let mut unlocked = context.this.unlocked.count(&mut prng);
                    let mut locked = context.this.locked.count(&mut prng);
                    context.barrier.wait();

                    while context.running.load(Ordering::SeqCst) {
                        context
                            .lock
                            .0
                            .with(|| (0..locked).for_each(|_| WorkUnit::work()));
                        iterations += 1;
                        (0..unlocked).for_each(|_| WorkUnit::work());

                        if iterations % 1024 == 0 {
                            unlocked = context.this.unlocked.count(&mut prng);
                            locked = context.this.locked.count(&mut prng);
                        }
                    }

                    iterations
                })
            })
            .collect::<Vec<_>>();

        context.barrier.wait();
        std::thread::sleep(self.measure);

        context.running.store(false, Ordering::SeqCst);
        let mut results = threads
            .into_iter()
            .map(|t| t.join().expect("failed to join OS thread"))
            .collect::<Vec<_>>();

        let sum = results
            .iter()
            .fold(0f64, |mean, &iters| mean + (iters as f64));

        let mean = sum.div(results.len() as f64);
        let mut stdev = results.iter().fold(0f64, |stdev, &iters| {
            let r = (iters as f64) - mean;
            stdev + (r * r)
        });
        if results.len() > 1 {
            stdev /= (results.len() - 1) as f64;
            stdev = stdev.sqrt();
        }

        results.sort();
        let min = results[0] as f64;
        let max = results[results.len() - 1] as f64;

        println!(
            "{:?}",
            BenchmarkResult {
                name: Some(L::NAME),
                mean: Some(mean),
                stdev: Some(stdev),
                min: Some(min),
                max: Some(max),
                sum: Some(sum),
            }
        );
    }
}

pub fn main() {
    let (measure, threads, locked, unlocked) = ArgParser::parse();
    let ns_per_work = WorkUnit::nanos_per_work();

    for &unlocked in unlocked.iter() {
        for &locked in locked.iter() {
            for &threads in threads.iter() {
                for &measure in measure.iter() {
                    let b = Benchmarker {
                        measure: measure,
                        threads: threads,
                        locked: locked.scaled(ns_per_work),
                        unlocked: unlocked.scaled(ns_per_work),
                    };

                    println!(
                        "measure={:?} threads={:?} locked={:?} unlocked={:?}\n{}\n{:?}",
                        measure,
                        threads,
                        locked,
                        unlocked,
                        "-".repeat(70),
                        BenchmarkResult::default(),
                    );

                    loom::model(move || {
                        let mut b = b;
                        bench_all(&mut b);
                    });

                    println!();
                }
            }
        }
    }
}
