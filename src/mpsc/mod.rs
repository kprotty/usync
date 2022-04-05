//! Multi-producer, single-consumer FIFO queue communication primitives.
//!
//! This module provides message-based communication over channels, concretely
//! defined among three types:
//!
//! * [`Sender`]
//! * [`SyncSender`]
//! * [`Receiver`]
//!
//! A [`Sender`] or [`SyncSender`] is used to send data to a [`Receiver`]. Both
//! senders are clone-able (multi-producer) such that many threads can send
//! simultaneously to one receiver (single-consumer).
//!
//! These channels come in two flavors:
//!
//! 1. An asynchronous, infinitely buffered channel. The [`channel`] function
//!    will return a `(Sender, Receiver)` tuple where all sends will be
//!    **asynchronous** (they never block). The channel conceptually has an
//!    infinite buffer.
//!
//! 2. A synchronous, bounded channel. The [`sync_channel`] function will
//!    return a `(SyncSender, Receiver)` tuple where the storage for pending
//!    messages is a pre-allocated buffer of a fixed size. All sends will be
//!    **synchronous** by blocking until there is buffer space available. Note
//!    that a bound of 0 is allowed, causing the channel to become a "rendezvous"
//!    channel where each sender atomically hands off a message to a receiver.
//!
//! [`send`]: Sender::send
//!
//! ## Disconnection
//!
//! The send and receive operations on channels will all return a [`Result`]
//! indicating whether the operation succeeded or not. An unsuccessful operation
//! is normally indicative of the other half of a channel having "hung up" by
//! being dropped in its corresponding thread.
//!
//! Once half of a channel has been deallocated, most operations can no longer
//! continue to make progress, so [`Err`] will be returned. Many applications
//! will continue to [`unwrap`] the results returned from this module,
//! instigating a propagation of failure among threads if one unexpectedly dies.
//!
//! [`unwrap`]: Result::unwrap
//!
//! # Examples
//!
//! Simple usage:
//!
//! ```
//! use std::thread;
//! use usync::mpsc::channel;
//!
//! // Create a simple streaming channel
//! let (tx, rx) = channel();
//! thread::spawn(move|| {
//!     tx.send(10).unwrap();
//! });
//! assert_eq!(rx.recv().unwrap(), 10);
//! ```
//!
//! Shared usage:
//!
//! ```
//! use std::thread;
//! use usync::mpsc::channel;
//!
//! // Create a shared channel that can be sent along from many threads
//! // where tx is the sending half (tx for transmission), and rx is the receiving
//! // half (rx for receiving).
//! let (tx, rx) = channel();
//! for i in 0..10 {
//!     let tx = tx.clone();
//!     thread::spawn(move|| {
//!         tx.send(i).unwrap();
//!     });
//! }
//!
//! for _ in 0..10 {
//!     let j = rx.recv().unwrap();
//!     assert!(0 <= j && j < 10);
//! }
//! ```
//!
//! Propagating panics:
//!
//! ```
//! use usync::mpsc::channel;
//!
//! // The call to recv() will return an error because the channel has already
//! // hung up (or been deallocated)
//! let (tx, rx) = channel::<i32>();
//! drop(tx);
//! assert!(rx.recv().is_err());
//! ```
//!
//! Synchronous channels:
//!
//! ```
//! use std::thread;
//! use usync::mpsc::sync_channel;
//!
//! let (tx, rx) = sync_channel::<i32>(0);
//! thread::spawn(move|| {
//!     // This will wait for the parent thread to start receiving
//!     tx.send(53).unwrap();
//! });
//! rx.recv().unwrap();
//! ```
//!
//! Unbounded receive loop:
//!
//! ```
//! use usync::mpsc::sync_channel;
//! use std::thread;
//!
//! let (tx, rx) = sync_channel(3);
//!
//! for _ in 0..3 {
//!     // It would be the same without thread and clone here
//!     // since there will still be one `tx` left.
//!     let tx = tx.clone();
//!     // cloned tx dropped within thread
//!     thread::spawn(move || tx.send("ok").unwrap());
//! }
//!
//! // Drop the last sender to stop `rx` waiting for message.
//! // The program will not complete if we comment this out.
//! // **All** `tx` needs to be dropped for `rx` to have `Err`.
//! drop(tx);
//!
//! // Unbounded receiver waiting for all senders to complete.
//! while let Ok(msg) = rx.recv() {
//!     println!("{}", msg);
//! }
//!
//! println!("completed");
//! ```
