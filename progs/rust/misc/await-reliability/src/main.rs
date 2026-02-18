async fn r#true() -> bool {
    true
}

async fn worker() {
    let mut i = 0;
    while r#true().await && i < 3 {
        print!("A");
        i += 1;
    }
}

fn main() {
    let w = std::pin::pin!(worker());
    let mut ctx = std::task::Context::from_waker(std::task::Waker::noop());
    print!("C");
    print!(" {:?}", w.poll(&mut ctx));
}
