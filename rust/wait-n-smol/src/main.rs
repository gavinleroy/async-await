use smol::prelude::*;
use smol::stream;

async fn wait_n<T, F>(futs: impl Iterator<Item = F>) -> Vec<T>
where
    T: Send + 'static,
    F: Future<Output = T> + Send + 'static,
{
    let handles = futs.map(smol::spawn).collect::<Vec<_>>();
    let mut v = vec![];
    for handle in handles {
        v.push(handle.await);
    }

    v
}

fn main() {
    smol::block_on(async {
        let timer = std::time::Instant::now();
        let futs = (0..=1000).map(std::future::ready);
        let ns = wait_n(futs).await;
        let res: usize = ns.iter().sum();
        assert_eq!(res, 500500);
        println!("done {}μs", timer.elapsed().as_micros());
    })
}
