use smol::prelude::*;

async fn race_n<T, F>(futs: impl Iterator<Item = F>) -> Option<T>
where
    T: Send + 'static,
    F: Future<Output = T> + Send + 'static,
{
    use smol::future::Boxed;
    use std::future::pending;

    let handles = futs.map(smol::spawn).collect::<Vec<_>>();
    if handles.is_empty() {
        return None;
    }

    let sentinel: Boxed<T> = Box::pin(pending::<T>().race(pending::<T>()));
    let res = handles
        .into_iter()
        .fold(sentinel, |r, t| Box::pin(r.race(t)))
        .await;

    Some(res)
}

fn main() {
    smol::block_on(async {
        let n = 42;
        let timer = std::time::Instant::now();
        let futs = (0..=1000).map(|i| async move {
            if i == n {
                i
            } else {
                std::future::pending::<usize>().await
            }
        });

        let res = race_n(futs).await;
        assert_eq!(res, Some(n));
        println!("done {}μs", timer.elapsed().as_micros());
    })
}
