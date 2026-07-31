// Figure 1-dev — Rust + smol (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never polled
//   ex2 END OF LIFE    spawn detached, extent ends un-awaited
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = smol::spawn on the global executor; smol tasks CANCEL when
//              their handle drops (the weak-reference design)
// timeout    = figlib::timeout: on expiry the future is DROPPED (Rust
//              cancellation-by-drop); a Task handle held inside cancels
//              its task
//
// Predicted: ex1 `C` (lazy: the future is never polled), ex2 `C` (weak:
// process_detached's handle drops at return, closing the task before its
// first poll — not even A prints), ex3 `AC` (the timeout drops the
// parent at 1 s; dropping its held handle cancels the child mid-sleep).

mod figlib;

use figlib::{sleep, timeout};

async fn write_to_log() {
    println!("A");
    // simulate log write
    sleep(2).await;
    println!("B");
}

async fn process_await() {
    let task = smol::spawn(write_to_log());
    sleep(0).await;
    task.await;
}

async fn process_detached() {
    let _task = smol::spawn(write_to_log());
    // handle drops at return: the task is cancelled
}

async fn ex1() {
    let _t = write_to_log(); // plain application: a future, never polled
    println!("C");
    sleep(3).await;
}

async fn ex2() {
    process_detached().await;
    sleep(1).await;
    println!("C");
}

async fn ex3() {
    timeout(1, process_await()).await;
    println!("C");
    sleep(3).await;
}

fn main() {
    smol::block_on(async {
        match std::env::args().nth(1).as_deref() {
            Some("1") => ex1().await,
            Some("2") => ex2().await,
            Some("3") => ex3().await,
            _ => panic!("expected ex number 1-3"),
        }
    });
}
