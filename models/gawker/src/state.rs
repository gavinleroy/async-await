use std::collections::BTreeMap;

use crate::trace::TraceEvent;

#[derive(Clone, Default)]
pub struct RuntimeState {
    pub tasks: BTreeMap<u64, TaskInfo>,
    pub threads: BTreeMap<u64, ThreadInfo>,
    pub timers: BTreeMap<u64, TimerInfo>,
    pub work_queue: Vec<u64>,
    pub stdout: String,
    pub config: BTreeMap<String, String>,
    pub src_highlight: Option<(usize, usize)>,
    pub active_task_region: Option<(usize, usize)>,
    pub block_region: Option<(usize, usize)>,
    pub executing_task: Option<u64>,
    /// task_id -> awaited_task_id (task A is waiting on task B to complete)
    pub await_deps: BTreeMap<u64, u64>,
    /// task_id -> awaited_promise_id (task A is waiting on promise P)
    pub promise_deps: BTreeMap<u64, u64>,
}

#[derive(Clone)]
pub struct TaskInfo {
    pub id: u64,
    pub parent_id: Option<u64>,
    pub children: Vec<u64>,
    pub status: TaskStatus,
    pub cancelled: bool,
    pub label: Option<String>,
    pub source: Option<String>,
    pub source_region: Option<(usize, usize)>,
    pub args: Vec<(String, String)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TaskStatus {
    Pending,
    Running,
    Suspended,
    Completed,
    Failed,
    Terminated,
}

impl TaskStatus {
    pub fn label(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Running => "running",
            Self::Suspended => "suspended",
            Self::Completed => "completed",
            Self::Failed => "failed",
            Self::Terminated => "terminated",
        }
    }
}

#[derive(Clone)]
pub struct ThreadInfo {
    pub tid: u64,
    pub current_task: Option<u64>,
}

#[derive(Clone)]
pub struct TimerInfo {
    pub promise_id: u64,
    pub deadline: f64,
    pub task_id: Option<u64>,
}

const CONFIG_KEYS: &[&str] = &[
    "eagerness",
    "suspension",
    "extent",
    "ref-strength",
    "destruction",
    "propagation",
    "awareness",
    "direction",
    "persistence",
    "pool-size",
];

impl RuntimeState {
    pub fn apply(&mut self, event: &TraceEvent) {
        match event.event_type.as_str() {
            "runtime:startup" => {
                self.config.clear();
                for &key in CONFIG_KEYS {
                    if let Some(val) = event.get_str(key) {
                        self.config.insert(key.into(), val.into());
                    } else if let Some(val) = event.get_u64(key) {
                        self.config.insert(key.into(), val.to_string());
                    }
                }
            }

            "task:create" => {
                if let Some(id) = event.get_u64("task-id") {
                    let parent_id = event.get_u64("parent-id");
                    let label = event.get_str("label").map(|s| s.to_string());
                    let source = event.get_str("source").map(|s| s.to_string());
                    let source_region = event
                        .fields
                        .get("source-pos")
                        .and_then(|v| v.as_i64())
                        .and_then(|pos| {
                            if pos > 0 {
                                let start = (pos - 1) as usize;
                                let len = source.as_ref().map(|s| s.len()).unwrap_or(0);
                                if len > 0 { Some((start, len)) } else { None }
                            } else {
                                None
                            }
                        });
                    let args = event
                        .fields
                        .get("args")
                        .and_then(|v| v.as_object())
                        .map(|obj| {
                            obj.iter()
                                .map(|(k, v)| {
                                    let val = match v {
                                        serde_json::Value::String(s) => s.clone(),
                                        other => other.to_string(),
                                    };
                                    (k.clone(), val)
                                })
                                .collect()
                        })
                        .unwrap_or_default();
                    self.tasks.insert(
                        id,
                        TaskInfo {
                            id,
                            parent_id,
                            children: Vec::new(),
                            status: TaskStatus::Pending,
                            cancelled: false,
                            label,
                            source,
                            source_region,
                            args,
                        },
                    );
                    if let Some(pid) = parent_id {
                        if let Some(parent) = self.tasks.get_mut(&pid) {
                            parent.children.push(id);
                        }
                    }
                }
            }

            "sched:enqueue" => {
                if let Some(id) = event.get_u64("task-id") {
                    if !self.work_queue.contains(&id) {
                        self.work_queue.push(id);
                    }
                }
            }

            "sched:thread-acquired" => {
                let worker_tid = event.get_u64("worker-tid");
                let task_id = event.get_u64("task-id");
                if let Some(w) = worker_tid {
                    self.threads
                        .entry(w)
                        .and_modify(|t| t.current_task = task_id)
                        .or_insert(ThreadInfo {
                            tid: w,
                            current_task: task_id,
                        });
                }
                if let Some(id) = task_id {
                    self.work_queue.retain(|&x| x != id);
                }
            }

            "sched:thread-released" => {
                if let Some(w) = event.get_u64("worker-tid") {
                    if let Some(thread) = self.threads.get_mut(&w) {
                        thread.current_task = None;
                    }
                }
            }

            "coro:resume" => {
                if let Some(id) = event.get_u64("task-id") {
                    if let Some(task) = self.tasks.get_mut(&id) {
                        task.status = TaskStatus::Running;
                    }
                    self.executing_task = Some(id);
                    self.await_deps.remove(&id);
                    self.promise_deps.remove(&id);
                }
            }

            "coro:suspended" => {
                if let Some(id) = event.get_u64("task-id") {
                    if let Some(task) = self.tasks.get_mut(&id) {
                        task.status = TaskStatus::Suspended;
                    }
                }
                self.executing_task = None;
                self.collect_stdout(event);
            }

            "coro:completed" | "coro:failed" => {
                self.executing_task = None;
                self.collect_stdout(event);
            }

            "task:settled" => {
                if let Some(id) = event.get_u64("task-id") {
                    if let Some(task) = self.tasks.get_mut(&id) {
                        task.status = match event.get_str("status") {
                            Some("completed") => TaskStatus::Completed,
                            _ => TaskStatus::Failed,
                        };
                    }
                }
            }

            "task:terminated" => {
                if let Some(id) = event.get_u64("task-id") {
                    if let Some(task) = self.tasks.get_mut(&id) {
                        task.status = TaskStatus::Terminated;
                    }
                }
            }

            "cancel:mark" => {
                if let Some(id) = event.get_u64("task-id") {
                    if let Some(task) = self.tasks.get_mut(&id) {
                        task.cancelled = true;
                    }
                }
            }

            "io:timer-register" => {
                if let (Some(promise_id), Some(deadline)) =
                    (event.get_u64("promise-id"), event.get_f64("deadline"))
                {
                    self.timers.insert(
                        promise_id,
                        TimerInfo {
                            promise_id,
                            deadline,
                            task_id: event.get_u64("task-id"),
                        },
                    );
                }
            }

            "io:timer-fired" | "io:timer-cancelled" => {
                if let Some(pid) = event.get_u64("promise-id") {
                    self.timers.remove(&pid);
                }
            }

            "exec:step" => {
                self.update_src_highlight(event);
                let fn_pos = event.fields.get("fn-source-pos").and_then(|v| v.as_i64());
                let fn_span = event.fields.get("fn-source-span").and_then(|v| v.as_i64());
                if let (Some(pos), Some(span)) = (fn_pos, fn_span) {
                    if pos > 0 && span > 0 {
                        self.active_task_region =
                            Some(((pos - 1) as usize, span as usize));
                    }
                }
            }

            "await:suspend" => {
                self.update_src_highlight(event);
                self.update_task_region_from_highlight();
                self.record_await_dep(event);
            }

            "await:fast-path" => {
                self.update_src_highlight(event);
                self.update_task_region_from_highlight();
                // fast-path: dependency resolved immediately, no ongoing dep
            }

            "await:inline-splice"
            | "cancel:request" | "spawn:task" | "spawn:existing" => {
                self.update_src_highlight(event);
                self.update_task_region_from_highlight();
            }

            "runtime:block-on" => {
                self.update_src_highlight(event);
                self.block_region = self.src_highlight;
            }

            "runtime:block-on-exit" | "runtime:shutdown" | "runtime:all-settled" => {
                if let Some(region) = self.block_region {
                    self.src_highlight = Some(region);
                    self.active_task_region = None;
                }
            }

            _ => {}
        }
    }

    fn update_src_highlight(&mut self, event: &TraceEvent) {
        let src_pos = event.fields.get("src-pos").and_then(|v| v.as_i64());
        let src_span = event.fields.get("src-span").and_then(|v| v.as_i64());
        if let (Some(pos), Some(span)) = (src_pos, src_span) {
            if pos > 0 && span > 0 {
                let offset = (pos - 1) as usize;
                let len = span as usize;
                self.src_highlight = Some((offset, len));
            }
        }
    }

    fn update_task_region_from_highlight(&mut self) {
        if let Some((offset, len)) = self.src_highlight {
            self.active_task_region = self.tasks.values().find_map(|t| {
                let (start, rlen) = t.source_region?;
                if offset >= start && offset + len <= start + rlen {
                    Some((start, rlen))
                } else {
                    None
                }
            });
        }
    }

    fn record_await_dep(&mut self, event: &TraceEvent) {
        if let Some(task_id) = event.get_u64("task-id") {
            if let Some(awaited) = event.get_u64("awaited-task") {
                self.await_deps.insert(task_id, awaited);
            } else if let Some(promise_id) = event.get_u64("awaited-promise") {
                self.promise_deps.insert(task_id, promise_id);
            }
        }
    }

    fn collect_stdout(&mut self, event: &TraceEvent) {
        if let Some(s) = event.get_str("stdout") {
            if !s.is_empty() {
                self.stdout.push_str(s);
            }
        }
    }

    pub fn root_tasks(&self) -> Vec<u64> {
        self.tasks
            .values()
            .filter(|t| t.parent_id.is_none())
            .map(|t| t.id)
            .collect()
    }
}
