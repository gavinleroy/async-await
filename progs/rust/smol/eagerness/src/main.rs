//Eagerness: Lazy
use std::{
    fmt::Display,
    sync::atomic::{AtomicUsize, Ordering},
};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    println!("{}", msg);
}

async fn async_int() -> i32 {
    let me = COUNTER.fetch_add(1, Ordering::SeqCst);
    let until = rand::random_range(0..50);

    for _ in 0..until {
        write(format!("{} waiting", me)).await;
    }

    until
}

fn main() {
    smol::block_on(async {
        let a = async_int();
        let b = async_int();
        println!("working");
        let c = a.await + b.await;
        write(c.to_string()).await;
    })
}
