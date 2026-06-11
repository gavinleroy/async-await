use std::collections::HashMap;

use ratatui::widgets::ListState;

use crate::state::RuntimeState;
use crate::trace::TraceEvent;

pub struct App {
    pub events: Vec<TraceEvent>,
    pub states: Vec<RuntimeState>,
    pub cursor: usize,
    pub running: bool,
    pub focus: Panel,
    pub event_list_state: ListState,
    pub thread_columns: Vec<u64>,
    pub thread_labels: HashMap<u64, String>,
    pub source_code: Option<String>,
    pub source_scroll: usize,
    pub detail_scroll: usize,
    pub task_scroll: usize,
    pub panel_areas: PanelAreas,
}

#[derive(Default, Clone)]
pub struct PanelAreas {
    pub events: Option<ratatui::layout::Rect>,
    pub tasks: Option<ratatui::layout::Rect>,
    pub source: Option<ratatui::layout::Rect>,
    pub detail: Option<ratatui::layout::Rect>,
}

#[derive(PartialEq, Eq)]
pub enum Panel {
    Events,
    Tasks,
    Source,
    Detail,
}

impl App {
    pub fn new(events: Vec<TraceEvent>, source_code: Option<String>) -> Self {
        let mut thread_labels: HashMap<u64, String> = HashMap::new();
        for event in &events {
            if event.event_type == "thread:register" {
                if let Some(role) = event.get_str("role") {
                    thread_labels.entry(event.tid).or_insert(role.to_string());
                }
            }
        }

        let sched_tids: Vec<u64> = events
            .iter()
            .filter(|e| {
                e.event_type == "thread:register"
                    && e.get_str("role").map_or(false, |r| r == "Sched")
            })
            .map(|e| e.tid)
            .collect();

        let all_events: Vec<TraceEvent> = events
            .into_iter()
            .filter(|e| e.event_type != "thread:register")
            .collect();

        // Build display events (no Sched) and states aligned to them.
        // Apply hidden Sched events to state but don't add them to events vec.
        let mut events: Vec<TraceEvent> = Vec::new();
        let mut states = Vec::new();
        let mut state = RuntimeState::default();
        states.push(state.clone());
        for event in all_events {
            state.apply(&event);
            if !sched_tids.contains(&event.tid) {
                events.push(event);
                states.push(state.clone());
            }
        }

        let mut thread_columns: Vec<u64> = Vec::new();
        for event in &events {
            if !thread_columns.contains(&event.tid) {
                thread_columns.push(event.tid);
            }
        }
        let mut unknown_count = 0u32;
        for &tid in &thread_columns {
            thread_labels.entry(tid).or_insert_with(|| {
                let label = format!("T{unknown_count}");
                unknown_count += 1;
                label
            });
        }

        // Finalizer always rightmost
        let finalizer_tid = thread_labels
            .iter()
            .find(|(_, v)| v.as_str() == "Finalizer")
            .map(|(&k, _)| k);
        if let Some(ftid) = finalizer_tid {
            thread_columns.retain(|&t| t != ftid);
            thread_columns.push(ftid);
        }

        App {
            events,
            states,
            cursor: 0,
            running: true,
            focus: Panel::Events,
            event_list_state: ListState::default().with_selected(Some(0)),
            thread_columns,
            thread_labels,
            source_code,
            source_scroll: 0,
            detail_scroll: 0,
            task_scroll: 0,
            panel_areas: PanelAreas::default(),
        }
    }

    pub fn current_state(&self) -> &RuntimeState {
        &self.states[self.cursor + 1]
    }

    pub fn current_event(&self) -> Option<&TraceEvent> {
        self.events.get(self.cursor)
    }

    pub fn step_forward(&mut self) {
        if self.cursor + 1 < self.events.len() {
            self.cursor += 1;
            self.event_list_state.select(Some(self.cursor));
        }
    }

    pub fn step_back(&mut self) {
        if self.cursor > 0 {
            self.cursor -= 1;
            self.event_list_state.select(Some(self.cursor));
        }
    }

    pub fn jump_start(&mut self) {
        self.cursor = 0;
        self.event_list_state.select(Some(0));
    }

    pub fn jump_end(&mut self) {
        if !self.events.is_empty() {
            self.cursor = self.events.len() - 1;
            self.event_list_state.select(Some(self.cursor));
        }
    }

    pub fn cycle_focus(&mut self) {
        self.focus = match self.focus {
            Panel::Events => Panel::Tasks,
            Panel::Tasks => Panel::Source,
            Panel::Source => Panel::Detail,
            Panel::Detail => Panel::Events,
        };
    }

    fn panel_at(&self, col: u16, row: u16) -> Option<Panel> {
        if let Some(r) = self.panel_areas.source {
            if col >= r.x && col < r.x + r.width && row >= r.y && row < r.y + r.height {
                return Some(Panel::Source);
            }
        }
        if let Some(r) = self.panel_areas.detail {
            if col >= r.x && col < r.x + r.width && row >= r.y && row < r.y + r.height {
                return Some(Panel::Detail);
            }
        }
        if let Some(r) = self.panel_areas.tasks {
            if col >= r.x && col < r.x + r.width && row >= r.y && row < r.y + r.height {
                return Some(Panel::Tasks);
            }
        }
        if let Some(r) = self.panel_areas.events {
            if col >= r.x && col < r.x + r.width && row >= r.y && row < r.y + r.height {
                return Some(Panel::Events);
            }
        }
        None
    }

    pub fn scroll_down_at(&mut self, col: u16, row: u16) {
        match self.panel_at(col, row) {
            Some(Panel::Source) => self.source_scroll = self.source_scroll.saturating_add(3),
            Some(Panel::Detail) => self.detail_scroll = self.detail_scroll.saturating_add(3),
            Some(Panel::Tasks) => self.task_scroll = self.task_scroll.saturating_add(1),
            Some(Panel::Events) => self.step_forward(),
            _ => self.step_forward(),
        }
    }

    pub fn scroll_up_at(&mut self, col: u16, row: u16) {
        match self.panel_at(col, row) {
            Some(Panel::Source) => self.source_scroll = self.source_scroll.saturating_sub(3),
            Some(Panel::Detail) => self.detail_scroll = self.detail_scroll.saturating_sub(3),
            Some(Panel::Tasks) => self.task_scroll = self.task_scroll.saturating_sub(1),
            Some(Panel::Events) => self.step_back(),
            _ => self.step_back(),
        }
    }

    pub fn scroll_down(&mut self) {
        match self.focus {
            Panel::Source => self.source_scroll = self.source_scroll.saturating_add(3),
            Panel::Detail => self.detail_scroll = self.detail_scroll.saturating_add(3),
            Panel::Tasks => self.task_scroll = self.task_scroll.saturating_add(1),
            _ => self.step_forward(),
        }
    }

    pub fn scroll_up(&mut self) {
        match self.focus {
            Panel::Source => self.source_scroll = self.source_scroll.saturating_sub(3),
            Panel::Detail => self.detail_scroll = self.detail_scroll.saturating_sub(3),
            Panel::Tasks => self.task_scroll = self.task_scroll.saturating_sub(1),
            _ => self.step_back(),
        }
    }
}
