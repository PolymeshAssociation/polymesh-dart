/// Assert that a `Result` is `Err`, that the error matches a given pattern, and optionally
/// that the error message contains a given string. These are just for testing.
macro_rules! assert_err {
    ($result:expr, $pattern:pat $(,)?) => {
        match &$result {
            Err(e) => {
                assert!(
                    matches!(e, $pattern),
                    "expected error matching `{}` but got: {:?}",
                    stringify!($pattern),
                    e
                );
            }
            Ok(_) => panic!("expected Err but got Ok"),
        }
    };
    ($result:expr, $pattern:pat, $msg_substr:expr $(,)?) => {
        match &$result {
            Err(e) => {
                assert!(
                    matches!(e, $pattern),
                    "expected error matching `{}` but got: {:?}",
                    stringify!($pattern),
                    e
                );
                let msg = format!("{}", e);
                assert!(
                    msg.contains($msg_substr),
                    "error message {:?} does not contain {:?}",
                    msg,
                    $msg_substr
                );
            }
            Ok(_) => panic!("expected Err but got Ok"),
        }
    };
}
