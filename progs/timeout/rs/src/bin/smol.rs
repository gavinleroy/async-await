use std::time::Duration;

use futures::FutureExt;
use smol::{Timer, future::FutureExt as _};

async fn sleep(duration: Duration) {
  Timer::after(duration).await;
}

async fn timeout<T>(duration: Duration, task: impl Future<Output = T>) -> Option<T> {
  task.map(Some).or(sleep(duration).map(|_| None)).await
}

async fn timeout_task<T, Fut>(duration: Duration, task: Fut) -> Option<T>
where
  T: Send + 'static,
  Fut: Future<Output = T> + Send + 'static,
{
  let mut handle = smol::spawn(task);
  let result = (&mut handle)
    .map(Some)
    .or(sleep(duration).map(|_| None))
    .await;
  if result.is_none() {
    handle.cancel().await;
  }
  result
}

fn main() {
  smol::block_on(async {
    println!(
      "{:#?}",
      timeout(Duration::from_secs(2), sleep(Duration::from_secs(1))).await
    );

    println!(
      "{:#?}",
      timeout(Duration::from_secs(1), sleep(Duration::from_secs(2))).await
    );

    println!(
      "{:#?}",
      timeout_task(Duration::from_secs(2), sleep(Duration::from_secs(1))).await
    );

    println!(
      "{:#?}",
      timeout_task(Duration::from_secs(1), sleep(Duration::from_secs(2))).await
    );
  })
}
