using System;
using System.Drawing;
using System.IO;
using System.Threading.Tasks;
using System.Windows.Forms;

namespace TextEditorCrash
{
    static class Program
    {
        [STAThread]
        static void Main()
        {
            Application.SetHighDpiMode(HighDpiMode.SystemAware);
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            // TEST: (Is this possible?) In production, you might have a global
            // exception handler here. However, `async void` exceptions often
            // bypass standard catches or corrupt the state so badly the app
            // must terminate anyway.
            Application.Run(new MainForm());
        }
    }

    // =================================================================================
    // 2. THE UI (MainForm)
    // =================================================================================
    public class MainForm : Form
    {
        private RichTextBox _editor;
        private StatusStrip _statusBar;
        private ToolStripStatusLabel _statusLabel;
        
        // Dependencies
        private DocumentManager _docManager;
        private AutoSaveController _autoSaveController;

        public MainForm()
        {
            this.Text = "ProText v1.0 (Unregistered)";
            this.Size = new Size(800, 600);

            InitializeComponent();
            InitializeServices();
        }

        private void InitializeComponent()
        {
            // Simple Layout: Text box takes up whole screen, Status bar at bottom
            _editor = new RichTextBox { Dock = DockStyle.Fill, Font = new Font("Consolas", 12) };
            _statusBar = new StatusStrip();
            _statusLabel = new ToolStripStatusLabel { Text = "Ready" };
            
            _statusBar.Items.Add(_statusLabel);
            this.Controls.Add(_editor);
            this.Controls.Add(_statusBar);

            // Bind text changes to trigger "Dirty" state
            _editor.TextChanged += (s, e) => _docManager.MarkDirty(_editor.Text);
        }

        private void InitializeServices()
        {
            // Composition Root
            var diskService = new DiskIO();
            _docManager = new DocumentManager();
            
            // We pass the UpdateStatus method so the background controller can talk to UI
            _autoSaveController = new AutoSaveController(_docManager, diskService, UpdateStatus);
            
            // Start the background timer
            _autoSaveController.StartAutoSaveTimer();
        }

        // Method to update UI safely from services
        public void UpdateStatus(string msg, bool isError)
        {
            _statusLabel.Text = msg;
            _statusLabel.ForeColor = isError ? Color.Red : Color.Black;
        }
    }

    // =================================================================================
    // 3. THE LOGIC (Domain Layer)
    // =================================================================================
    public class DocumentManager
    {
        public string Content { get; private set; } = "";
        public string FilePath { get; private set; } = "C:\\Temp\\Untitled.txt";
        public bool IsDirty { get; set; } = false;

        public void MarkDirty(string newContent)
        {
            Content = newContent;
            IsDirty = true;
        }

        public void MarkSaved()
        {
            IsDirty = false;
        }
    }

    public class DiskIO
    {
        public async Task SaveFileAsync(string path, string content)
        {
            // Simulate standard IO overhead
            await Task.Delay(500);

            // SIMULATED HARDWARE FAILURE
            // In a real world, this could be "Disk Full", "Permission Denied", or "Network Share Lost"
            throw new IOException($"Target Volume C: is out of space. Unable to write to {path}.");
        }
    }

    public class AutoSaveController
    {
        private readonly DocumentManager _doc;
        private readonly DiskIO _disk;
        private readonly Action<string, bool> _uiCallback;
        private readonly System.Windows.Forms.Timer _timer;

        public AutoSaveController(DocumentManager doc, DiskIO disk, Action<string, bool> uiCallback)
        {
            _doc = doc;
            _disk = disk;
            _uiCallback = uiCallback;

            // Setup a timer to fire every 5 seconds
            _timer = new System.Windows.Forms.Timer();
            _timer.Interval = 5000; 
            _timer.Tick += AutoSaveTimer_Tick; // <--- SUBSCRIBING TO THE EVENT
        }

        public void StartAutoSaveTimer()
        {
            _timer.Start();
            _uiCallback("Auto-save enabled (every 5s)... type something!", false);
        }

        private async void AutoSaveTimer_Tick(object sender, EventArgs e)
        {
            if (!_doc.IsDirty) return;

            _uiCallback("Auto-saving...", false);
            await _disk.SaveFileAsync(_doc.FilePath, _doc.Content);
            _doc.MarkSaved();
            _uiCallback($"Saved at {DateTime.Now:T}", false);
        }
    }
}
