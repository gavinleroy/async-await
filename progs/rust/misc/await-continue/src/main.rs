use std::{
    collections::HashSet,
    sync::{Arc, Mutex},
    time::Duration,
};
use tokio::time::sleep;

async fn r#true() -> bool {
    true
}

async fn work(report: impl Fn()) {
    let mut i = 0;
    while r#true().await && i < 10 {
        report();
        i += 1;
    }
}

async fn async_main<F>(print: F)
where
    F: Fn(&str) + Send + Sync + Clone + 'static,
{
    let print2 = print.clone();
    let print3 = print.clone();

    let p1 = work(move || print("A"));
    let p2 = work(move || print2("B"));

    print3("C");

    let p1 = tokio::spawn(p1);
    let p2 = tokio::spawn(p2);

    print3("C");

    p1.await;
    p2.await;
}

#[derive(Clone)]
struct Buffer {
    data: Arc<Mutex<String>>,
}

impl Buffer {
    fn new() -> Self {
        Buffer {
            data: Arc::new(Mutex::new(String::new())),
        }
    }

    fn write(&self, msg: &str) {
        let mut data = self.data.lock().unwrap();
        data.push_str(msg);
    }

    fn take(&self) -> String {
        let mut data = self.data.lock().unwrap();
        std::mem::take(&mut *data)
    }
}

fn main() {
    let mut set = HashSet::new();
    let buf = Buffer::new();
    for _ in 0..1000 {
        let b = buf.clone();
        //tokio::runtime::Builder::new_multi_thread()
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(async_main(move |s| b.write(s)));
        set.insert(buf.take());
    }

    println!("{:#?}", set);
}
