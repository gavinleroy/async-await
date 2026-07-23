// Figure 1 — Rust + smol (timeout variant).
//
// spawn      = smol::spawn on the global executor; "spawn and ignore" is
//              `let _ = smol::spawn(...)` — the handle drops immediately,
//              and smol tasks CANCEL on drop
// timeout    = figlib::timeout: future::or racing the future against a
//              timer — on expiry the future is dropped; a Task handle
//              held inside it cancels its task
// isolation  = one block_on; each ex ends with a 3 s grace sleep so any
//              surviving work lands in its own ex's section.
//
// Predicted: ex1 `ε` (the ignored task's handle drops before its first
// poll), ex2 `A` (the inner task prints A at t0; the timeout drops
// process_await at 0.1 s, whose held handle cancels it mid-sleep),
// ex3 `ε` (inner handle dropped instantly, as in ex1).

mod figlib;

use figlib::{sleep, timeout};

fn grace() -> f64 {
    std::env::var("GRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(3.0)
}

async fn write_to_log() {
    println!("A");
    // simulate log write
    sleep(0.2).await;
    println!("B");
}

async fn process_ignore() {
    let _ = smol::spawn(write_to_log()); // spawn, handle dropped: cancels
    sleep(0.0).await; // do other work ...
}

async fn process_await() {
    let task = smol::spawn(write_to_log()); // spawn
    // do other work ...
    let _ = task.await;
}

async fn ex1() {
    process_ignore().await;
}

async fn ex2() {
    timeout(0.1, process_await()).await;
}

async fn ex3() {
    timeout(0.1, process_ignore()).await;
}

fn main() {
    smol::block_on(async {
        match std::env::args().nth(1).as_deref() {
            Some("1") => ex1().await,
            Some("2") => ex2().await,
            Some("3") => ex3().await,
            _ => panic!("expected ex number 1-3"),
        }
        sleep(grace()).await;
    });
}
