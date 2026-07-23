// Figure library — smol.
//
// sleep(seconds): the lane's sleep, shared by all figure programs.
// timeout(seconds, fut): race the future against a timer (future::or, the
// select of the smol ecosystem). On expiry the future is DROPPED
// (cancellation-by-drop) — and unlike tokio, dropping a smol Task handle
// held inside it CANCELS that task; only detached tasks keep running.

use smol::Timer;
use std::future::Future;
use std::time::Duration;

pub async fn sleep(seconds: f64) {
    Timer::after(Duration::from_secs_f64(seconds)).await;
}

pub async fn timeout<F: Future<Output = ()>>(seconds: f64, fut: F) {
    smol::future::or(fut, sleep(seconds)).await;
}
