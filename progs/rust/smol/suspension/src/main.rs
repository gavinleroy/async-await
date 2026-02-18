//Suspension: Dynamic
use std::{
    fmt::Display,
    sync::atomic::{AtomicUsize, Ordering},
};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

async fn r#continue() -> bool {
    true
}

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    print!("{msg}");
}

async fn async_int() -> i32 {
    let me = COUNTER.fetch_add(1, Ordering::SeqCst);
    let until = rand::random_range(0..5000);

    for _ in 0..until {
        if !r#continue().await {
            break;
        }
        write(format!("{me}")).await;
    }
    write(format!("{me} done")).await;

    until
}

// NOTE, the SMOL executor is single-threaded by default
fn main() {
    smol::block_on(async {
        let a = smol::spawn(async_int());
        let b = smol::spawn(async_int());
        println!("working");
        let c = a.await + b.await;
        write(c.to_string()).await;
    })
}
