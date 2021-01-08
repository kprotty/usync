#[macro_export]
macro_rules! cfg_if {
    // match if/else chains with a final `else`
    ($(
        if #[cfg($meta:meta)] { $($tokens:tt)* }
    ) else * else {
        $($tokens2:tt)*
    }) => {
        $crate::cfg_if! {
            @__items
            () ;
            $( ( ($meta) ($($tokens)*) ), )*
            ( () ($($tokens2)*) ),
        }
    };

    // match if/else chains lacking a final `else`
    (
        if #[cfg($i_met:meta)] { $($i_tokens:tt)* }
        $(
            else if #[cfg($e_met:meta)] { $($e_tokens:tt)* }
        )*
    ) => {
        $crate::cfg_if! {
            @__items
            () ;
            ( ($i_met) ($($i_tokens)*) ),
            $( ( ($e_met) ($($e_tokens)*) ), )*
            ( () () ),
        }
    };

    // Internal and recursive macro to emit all the items
    //
    // Collects all the negated cfgs in a list at the beginning and after the
    // semicolon is all the remaining items
    (@__items ($($not:meta,)*) ; ) => {};
    (@__items ($($not:meta,)*) ; ( ($($m:meta),*) ($($tokens:tt)*) ), $($rest:tt)*) => {
        // Emit all items within one block, applying an appropriate #[cfg]. The
        // #[cfg] will require all `$m` matchers specified and must also negate
        // all previous matchers.
        #[cfg(all($($m,)* not(any($($not),*))))] $crate::cfg_if! { @__identity $($tokens)* }

        // Recurse to emit all other items in `$rest`, and when we do so add all
        // our `$m` matchers to the list of `$not` matchers as future emissions
        // will have to negate everything we just matched as well.
        $crate::cfg_if! { @__items ($($not,)* $($m,)*) ; $($rest)* }
    };

    // Internal macro to make __apply work out right for different match types,
    // because of how macros matching/expand stuff.
    (@__identity $($tokens:tt)*) => {
        $($tokens)*
    };
}
