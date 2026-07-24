// Figure library — tokio.
//
// sleep(seconds): the lane's sleep, shared by all figure programs.
// timeout(seconds, fut): tokio's built-in. On expiry the future is DROPPED
// (Rust cancellation-by-drop). Dropping a JoinHandle held inside it does
// NOT stop the spawned task — tokio tasks keep running detached.

use std::future::Future;
use std::time::Duration;

pub async fn sleep(seconds: u64) {
    tokio::time::sleep(Duration::from_secs(seconds)).await;
}

pub async fn timeout<F: Future<Output = ()>>(seconds: u64, fut: F) {
    tokio::select! {
        () = fut => {}
        () = sleep(seconds) => {}
    }
}
