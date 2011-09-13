// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Container;
import java.awt.Cursor;
import java.awt.EventQueue;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.GridBagLayout;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.Box;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;
import javax.swing.JViewport;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;
import javax.swing.ToolTipManager;
import javax.swing.WindowConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.MouseInputAdapter;

import de.uka.ilkd.key.gui.actions.AbandonTaskAction;
import de.uka.ilkd.key.gui.actions.AboutAction;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.gui.actions.EditMostRecentFileAction;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.gui.actions.FontSizeAction;
import de.uka.ilkd.key.gui.actions.LemmaGenerationBatchModeAction;
import de.uka.ilkd.key.gui.actions.LicenseAction;
import de.uka.ilkd.key.gui.actions.LemmaGenerationAction;
import de.uka.ilkd.key.gui.actions.LemmaGenerationAction.Mode;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.actions.MinimizeInteraction;
import de.uka.ilkd.key.gui.actions.OneStepSimplificationToggleAction;
import de.uka.ilkd.key.gui.actions.OpenExampleAction;
import de.uka.ilkd.key.gui.actions.OpenFileAction;
import de.uka.ilkd.key.gui.actions.OpenMostRecentFileAction;
import de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction;
import de.uka.ilkd.key.gui.actions.ProofManagementAction;
import de.uka.ilkd.key.gui.actions.SMTOptionsAction;
import de.uka.ilkd.key.gui.actions.SaveFileAction;
import de.uka.ilkd.key.gui.actions.ShowActiveSettingsAction;
import de.uka.ilkd.key.gui.actions.ShowActiveTactletOptionsAction;
import de.uka.ilkd.key.gui.actions.ShowKnownTypesAction;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.actions.ShowUsedContractsAction;
import de.uka.ilkd.key.gui.actions.TacletOptionsAction;
import de.uka.ilkd.key.gui.actions.ToolTipOptionsAction;
import de.uka.ilkd.key.gui.actions.UndoLastStepAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.ExitKeYEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.smt.ComplexButton;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.PreferenceSaver;


@SuppressWarnings("serial")
public final class MainWindow extends JFrame  {

    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;
    
    /** size of the tool bar icons */
    public static final int TOOLBAR_ICON_SIZE = 15;
    
    /** the tab bar at the left */
    private JTabbedPane tabbedPane;
    
    /** the first toolbar */
    private JToolBar controlToolBar;

    /** the second toolbar */
    private JToolBar fileOpToolBar;
    
    /** the current goal view */
    private JScrollPane goalView;

    /** the current proof tree*/
    private ProofTreeView proofTreeView;

    /** the list of current open goals*/
    private JScrollPane openGoalsView;
    
    /** the view of a sequent */
    private SequentView sequentView;
    
    /** the rule view */
    private RuleView ruleView = null;
    
    /** the strategy selection view */
    private StrategySelectionView strategySelectionView = null;
   
    /** contains a list of all proofs */
    private JScrollPane proofListView;
    
    private TaskTree proofList;
    
    /** list of open goals of the current proof */
    private GoalList goalList;
    
    /** the mediator is stored here */
    private KeYMediator mediator;
    
    /** the user interface which direct all notifications to this window */ 
    private UserInterface userInterface;
    
    /** the status line */
    private MainStatusLine statusLine;
    
    /** the main progress monitor */
//    private ProgressMonitor progressMonitor = new MainProgressMonitor();
    
    /** listener to global proof events */
    private MainProofListener proofListener;
    
    /** listener to gui events */
    private MainGUIListener guiListener;
    private RecentFileMenu recentFiles;
    
    public boolean frozen = false;
   
    private static final String PARA = 
       "<p style=\"font-family: lucida;font-size: 12pt;font-weight: bold\">";
       
    /** action for starting and stopping automatic mode */
    private MainWindowAction autoModeAction;
    
    /** action for opening a KeY file */
    private MainWindowAction openFileAction;
    
    /** action for opening an example */
    private OpenExampleAction openExampleAction;    
    
    /** action for opening the most recent KeY file */
    private OpenMostRecentFileAction openMostRecentFileAction;
    
    /** action for editing the most recent KeY file */
    private EditMostRecentFileAction editMostRecentFileAction;    
    
    /** action for saving a proof (attempt) */
    private SaveFileAction saveFileAction;
    
    /** action for opening the proof management dialog */
    private ProofManagementAction proofManagementAction;
    
    /** action for loading taclets onto a ongoing proof */
    private LemmaGenerationAction loadUserDefinedTacletsAction;
    private LemmaGenerationAction loadUserDefinedTacletsForProvingAction;
    private LemmaGenerationAction loadKeYTaclets;
    private LemmaGenerationBatchModeAction lemmaGenerationBatchModeAction;
    

    
    private OneStepSimplificationToggleAction oneStepSimplAction = 
        new OneStepSimplificationToggleAction(this);
    
    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";

    /** Determines if the KeY prover is started in visible mode*/
    public static boolean visible = true;
    

    
    /** for locking of threads waiting for the prover to exit */
    public final Object monitor = new Object();
    
    public static MainWindow instance = null;    
    
//    private ProverTaskListener taskListener;
    
    private NotificationManager notificationManager;
    
    private PreferenceSaver prefSaver = 
        new PreferenceSaver(Preferences.userNodeForPackage(MainWindow.class));

    private ComplexButton smtComponent;
    
    /** The menu for the SMT solver options */
    public final JMenu smtOptions = new JMenu("SMT Solvers...");

    private ExitMainAction exitMainAction;

    private ShowActiveSettingsAction showActiveSettingsAction;

    /**
     * creates prover -- private, use {@link #createInstance(String)}
     * 
     */
    private MainWindow() {
    }
    
    /**
     * initialize the singleton object of this class.
     * 
     * @param title
     *            the frame's title
     */
    private void initialize(String title) {
        setTitle(title);
        setIconImage(IconFactory.keyLogo());
        setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        proofListener = new MainProofListener();
        guiListener = new MainGUIListener();
        
        // will be: userInterface = new WindowUserInterface(this);
        userInterface = Main.makeUserInterface();
        
//        taskListener = (Main.batchMode ? (ProverTaskListener)
//                new MainTaskListenerBatchMode() : 
//            (ProverTaskListener) new MainTaskListener());
        
        setMediator(new KeYMediator(this));
        
        initNotification();
        layoutMain();
        
        SwingUtilities.updateComponentTreeUI(this);
        ToolTipManager.sharedInstance().setDismissDelay(30000);
        
        addWindowListener(exitMainAction.windowListener);
        
    }
    
    private void initNotification() {
        if (!Main.batchMode) {
            notificationManager = new NotificationManager(mediator);
        }
    }
    
//    public void updateUI() {
//        if (goalView != null)
//            goalView.updateUI();
//        if (proofView != null)
//            proofView.updateUI();
//        if (openGoalsView != null)
//            openGoalsView.updateUI();
//        if (ruleView != null)
//            ruleView.updateUI();
//        if (proofListView != null)
//            proofListView.updateUI();
//    }
    
    public ProblemInitializer createProblemInitializer(){
        ProblemInitializer pi = new ProblemInitializer(getUserInterface(),
                getMediator().getProfile(), new Services(getMediator()
                        .getExceptionHandler()), true, getUserInterface());
        return pi;
    }
    
    /**
     * sets the mediator to corresspond with other gui elements
     * 
     * @param m
     *            the KeYMediator
     */
    private void setMediator(KeYMediator m) {
        assert mediator == null;
	// This was an incomplete replacement method. It would call first
	// "unregisterMediatorListeners();"
        mediator = m;
        
        registerMediatorListeners();
    }
    
    /** register several listeners */
    private void registerMediatorListeners() {
        mediator.addKeYSelectionListener(proofListener);
        mediator.addAutoModeListener(proofListener);
        mediator.addGUIListener(guiListener);
    }
    
//    /** unregister several listeners */
//    private void unregisterMediatorListeners() {
//        mediator.removeKeYSelectionListener(proofListener);
//        mediator.removeAutoModeListener(proofListener);
//        mediator.removeGUIListener(guiListener);
//    }
    
    /**
     * return the mediator
     * 
     * @return the mediator
     */
    public KeYMediator getMediator() {
        return mediator;
    }
    
    public void setVisible(boolean v){
        super.setVisible(v && visible);
    }
    
    /** initialised, creates GUI and lays out the main frame */
    private void layoutMain() {
        // set overall layout manager
        getContentPane().setLayout(new BorderLayout());
        
        // FIXME FIXME
        recentFiles = new RecentFileMenu(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                loadProblem(new File(recentFiles.getAbsolutePath((JMenuItem) e.getSource())));
            }
        }, MAX_RECENT_FILES, null);
        recentFiles.load(PathConfig.RECENT_FILES_STORAGE);
        
        
        // FIXME do this NOT in layout of GUI
        // minimize interaction
        final boolean stupidMode = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().tacletFilter();
        mediator.setStupidMode(stupidMode);
        
        // set up actions
        autoModeAction            = new AutoModeAction(this);
        openFileAction            = new OpenFileAction(this);
        openExampleAction         = new OpenExampleAction(this);
        openMostRecentFileAction  = new OpenMostRecentFileAction(this);
        editMostRecentFileAction  = new EditMostRecentFileAction(this);
        saveFileAction            = new SaveFileAction(this);
        proofManagementAction     = new ProofManagementAction(this);
        exitMainAction            = new ExitMainAction(this);
        showActiveSettingsAction  = new ShowActiveSettingsAction(this);
        loadUserDefinedTacletsAction = new LemmaGenerationAction.ProveAndAddTaclets(this);
        loadUserDefinedTacletsForProvingAction = new LemmaGenerationAction.ProveUserDefinedTaclets(this);
        loadKeYTaclets            = new LemmaGenerationAction.ProveKeYTaclets(this);
        lemmaGenerationBatchModeAction    = new LemmaGenerationBatchModeAction(this);
        
       // proveTacletsAction       = new ProveTacletsAction(this);
        
	
	
	mediator.addKeYSelectionListener(OneStepSimplifier.INSTANCE);
        

	// create empty views
	createViews();
	
	// create the contents of the views
	createProofElements();

	// create menubar
	JMenuBar bar = createMenuBar();
	setJMenuBar(bar);

	// create tool bars 
	controlToolBar = createProofControlToolBar();
        fileOpToolBar = createFileOpsToolBar();
        
        JPanel toolBarPanel = new JPanel();
        toolBarPanel.setLayout(new FlowLayout(FlowLayout.LEADING));
        toolBarPanel.add(controlToolBar);
        toolBarPanel.add(fileOpToolBar);
        
        // FIXME double entry?
        getContentPane().add(GuiUtilities.getClipBoardArea(), BorderLayout.PAGE_START);
        getContentPane().add(toolBarPanel, BorderLayout.PAGE_START);
        
        // create tabbed pane
        tabbedPane = createTabbedPane();

        proofListView.setPreferredSize(new java.awt.Dimension(250, 100));
        GuiUtilities.paintEmptyViewComponent(proofListView, "Proofs");
        
        JSplitPane leftPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, proofListView, tabbedPane);
        leftPane.setName("leftPane");
        leftPane.setOneTouchExpandable(true);
        
        JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftPane, goalView);
        splitPane.setResizeWeight(0); // the right pane is more important
        splitPane.setOneTouchExpandable(true);
        splitPane.setName("splitPane");
        getContentPane().add(splitPane, BorderLayout.CENTER);
        
//      // work around bug in
//      // com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
//      // removed since together is no longer supported (mulbrich 2011)        
//        {
//            public void setUI(javax.swing.plaf.SplitPaneUI ui) {
//                try {
//                    super.setUI(ui);
//                } catch (NullPointerException e) {
//                    Debug.out("Exception thrown by class Main at setUI");
//                }
//            }
//        }; 
        
        statusLine = new MainStatusLine("<html>" + PARA + Main.COPYRIGHT + PARA
                + "KeY is free software and comes with ABSOLUTELY NO WARRANTY."
                + " See About | License.", getFont());
        getContentPane().add(statusLine, BorderLayout.SOUTH);
        
     // FIXME put this somewhere descent
        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_C, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()), 
        "copy");
        goalView.getActionMap().put("copy", new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                GuiUtilities.copyHighlightToClipboard(sequentView);
            }
        });
        
        // default size
        setSize(1000, 750);
        setName("mainWindow");
        
        // load preferred sizes from system preferences
        prefSaver.load(this);
    }

    private JTabbedPane createTabbedPane() {
	JTabbedPane pane = new JTabbedPane();
	pane.addTab("Proof", null, proofTreeView,
	        "The current state of the proof as tree");
	pane.addTab("Goals", null, openGoalsView,
	        "The currently open goals");
	pane.addTab("Proof Search Strategy", null, strategySelectionView,
	        "Select strategy for automated proof search");
	pane.addTab("Rules", null, new JScrollPane(ruleView),
	        "All available rules");
	
        pane.setSelectedIndex(0);
        pane.setPreferredSize(new java.awt.Dimension(250, 440));
        
        // change some key mappings which collide with font settings.
	pane.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
	        .getParent().remove(
	                KeyStroke.getKeyStroke(KeyEvent.VK_UP, Toolkit
	                        .getDefaultToolkit().getMenuShortcutKeyMask()));
	pane.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(
	        KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, Toolkit
	                .getDefaultToolkit().getMenuShortcutKeyMask()));
	pane.setName("leftTabbed");
	
	return pane;
    }

    private JToolBar createFileOpsToolBar() {
	JToolBar fileOperations = new JToolBar("File Operations");        
        fileOperations.add(openFileAction);
        fileOperations.add(openMostRecentFileAction);
        fileOperations.add(editMostRecentFileAction);
        fileOperations.add(saveFileAction);        
        fileOperations.addSeparator();
        fileOperations.add(proofManagementAction);
	
        return fileOperations;
    }
    
    private JToolBar createProofControlToolBar() {
	JToolBar toolBar = new JToolBar("Proof Control");
	toolBar.setFloatable(true);
        toolBar.setRollover(true);

	toolBar.add(createWiderAutoModeButton());
        toolBar.addSeparator();                        
        toolBar.addSeparator();
        toolBar.addSeparator();
        ComplexButton comp = createSMTComponent();
        toolBar.add(comp.getActionComponent());
        toolBar.add(comp.getSelectionComponent());
        toolBar.addSeparator();
        toolBar.add(new UndoLastStepAction(this, false));
        JToggleButton oneStep = new JToggleButton(oneStepSimplAction);
        oneStep.setHideActionText(true);
        toolBar.addSeparator();
        toolBar.add(oneStep);
	return toolBar;
    }
    
    private void createViews() {
	goalView = new JScrollPane();
	GuiUtilities.paintEmptyViewComponent(goalView, "Current Goal");	

//	proofView = new JPanel();
//        proofView.setLayout(new BorderLayout(0,0));
       
//	paintEmptyViewComponent(proofView, "Proof");

	openGoalsView = new JScrollPane();
	GuiUtilities.paintEmptyViewComponent(openGoalsView, "Open Goals");
	
        proofListView = new JScrollPane();

	strategySelectionView = new StrategySelectionView(this);
	if ( mediator != null ) {
	    strategySelectionView.setMediator(mediator);
	}

	ruleView = new RuleView ();
	if ( mediator != null ) {
	    ruleView.setMediator(mediator);
	}
	
        Config.DEFAULT.setDefaultFonts();
        sequentView = new SequentView(mediator);
    }
    
    private ComplexButton createSMTComponent() {
	smtComponent= new ComplexButton(TOOLBAR_ICON_SIZE);
	smtComponent.setEmptyItem("No solver available","<html>No SMT solver is applicable for KeY.<br><br>If a solver is installed on your system," +
		"<br>please configure the KeY-System accordingly:\n" +
		"<br>Options|SMT Solvers</html>");

	smtComponent.setPrefix("Run ");
	
	smtComponent.addListener(new ChangeListener() {
	    
	    public void stateChanged(ChangeEvent e) {
		ComplexButton but = (ComplexButton) e.getSource();
		if(but.getSelectedItem() instanceof SMTInvokeAction){
		    SMTInvokeAction action = (SMTInvokeAction) but.getSelectedItem(); 
		    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().setActiveSolverUnion(action.solverUnion);
		}
	
	    }
	});

	updateSMTSelectMenu();
	mediator.addKeYSelectionListener(new DPEnableControl());
	return smtComponent;
    }
    
    private JComponent createWiderAutoModeButton() {
        JButton b = new JButton(autoModeAction);
        b.putClientProperty("hideActionText", Boolean.TRUE);
        //the following rigmarole is to make the button slightly wider
        JPanel p = new JPanel();
        p.setLayout(new GridBagLayout());
        p.add(b);
        return p;    
    }
    
//    public ProverTaskListener getProverTaskListener() {
//        return taskListener;
//    }
    
    /**
     * @return the status line object
     */
    public MainStatusLine getStatusLine () {
	return statusLine;
    }
    
    private void setStandardStatusLineImmediately() {
        statusLine.reset();
    }
    
    /**
     * Make the status line display a standard message, make progress bar and abort button invisible
     */
    public void setStandardStatusLine() {
        GuiUtilities.invokeOnEventQueue(new Runnable() {
	    public void run() {
		setStandardStatusLineImmediately();
	    }
	});
    }
    
    private void setStatusLineImmediately(String str, int max) {
        statusLine.reset();
        statusLine.setStatusText(str);
        if(max > 0) {
            getStatusLine().setProgressBarMaximum(max);
            statusLine.setProgressPanelVisible(true);
        } else {
            statusLine.setProgressPanelVisible(false);
        }
        statusLine.validate();
        statusLine.paintImmediately(0, 0, statusLine.getWidth(), statusLine.getHeight());
    }
    
    /**
     * Display the given message in the status line, make progress bar and abort button visible, set
     * the progress bar range to the given value, set the current progress to zero
     */
    public void setStatusLine(final String str, final int max) {
        GuiUtilities.invokeOnEventQueue(new Runnable() {
	    public void run() {
		setStatusLineImmediately(str, max);
	    }
	});
    }
    
    /**
     * Display the given message in the status line, make progress bar and abort button invisible
     */
    public void setStatusLine(String s) {
	setStatusLine(s, 0);
    }
    
//    /**
//     * Get the progress monitor that will update a progress bar in a corner of the main window.
//     */
//    public ProgressMonitor getProgressMonitor() {
//        return progressMonitor;
//    }
    
    /**
     * Freeze the main window by blocking all input events, except those for the status line (i.e.
     * the abort button within the status line)
     */
    public void freezeExceptAutoModeButton() {
        if (!frozen) {
            frozen = true;
            
            Component glassPane = new BlockingGlassPane(getContentPane());
            setGlassPane(glassPane);
            glassPane.setVisible(true);
        }
    }
    
    public void unfreezeExceptAutoModeButton() {
        if (frozen) {
            getGlassPane().setVisible(false);
            frozen = false;
        }
    }
    
 
    public void makePrettyView() {
        if (getMediator().ensureProofLoadedSilent()) {
            getMediator().getNotationInfo().refresh(mediator.getServices());
            getMediator().getProof().fireProofGoalsChanged();
        }        
    }
    
    /**
     * Return a list of aspects compiled into the system, one by line. The idea is that the aspects
     * will advise this method to add themselves to the list.
     */
    public String compiledAspects() {
        return "";
    }
    
    /** the number of goals the goal list currently contains */
    public int displayedOpenGoalNumber() {
        return goalList.getModel().getSize();
    }
    
    /**
     * create the goal list, proof tree, proof list. Add to their respective
     * containers.
     */
    private void createProofElements() {
	
	proofList = new TaskTree(mediator);
	
        proofTreeView = new ProofTreeView(mediator);
	proofTreeView.setSize(proofTreeView.getPreferredSize());
	proofTreeView.setVisible(true);
        
	goalList = new GoalList(mediator);
        // FIXME IS that needed?
        goalList.setSize(goalList.getPreferredSize());
        openGoalsView.setViewportView(goalList);
    }
    
    private void addToProofList(de.uka.ilkd.key.proof.ProofAggregate plist) {
        proofList.addProof(plist);
        // GUI
        proofList.setSize(proofList.getPreferredSize());
        proofListView.setViewportView(proofList);
    }
    
    /** creates menubar entries and adds them to menu bar */
    private JMenuBar createMenuBar() {
        JMenuBar menuBar = new JMenuBar();
        menuBar.add(createFileMenu());
        menuBar.add(createViewMenu());
        menuBar.add(createProofMenu());
        menuBar.add(createOptionsMenu());
        menuBar.add(Box.createHorizontalGlue());
        menuBar.add(createHelpMenu());
        if (Debug.ENABLE_DEBUG)
            menuBar.add(createDebugMenu());
        return menuBar;
    }

    private JMenu createFileMenu() {
        JMenu fileMenu = new JMenu("File");
        fileMenu.setMnemonic(KeyEvent.VK_F);
        
        fileMenu.add(openExampleAction);
        fileMenu.add(openFileAction);
        fileMenu.add(openMostRecentFileAction);
        fileMenu.add(editMostRecentFileAction);        
        fileMenu.add(saveFileAction);
        fileMenu.addSeparator();
        fileMenu.add(proofManagementAction);
        
        
        fileMenu.add(loadUserDefinedTacletsAction);
        JMenu submenu = new JMenu("Prove...");
        fileMenu.add(submenu);
        
        submenu.add(loadUserDefinedTacletsForProvingAction);
        submenu.add(loadKeYTaclets);
        submenu.add(lemmaGenerationBatchModeAction);
        fileMenu.addSeparator();
        fileMenu.add(recentFiles.getMenu());
        fileMenu.addSeparator();
        fileMenu.add(exitMainAction);
        return fileMenu;
    }
    
    private JMenu createViewMenu() {
        JMenu view = new JMenu("View");
        view.setMnemonic(KeyEvent.VK_V);
        
        view.add(new JCheckBoxMenuItem(new PrettyPrintToggleAction(this)));
        view.addSeparator();
        {
            JMenu fontSize = new JMenu("Font Size");
            fontSize.add(new FontSizeAction(this, FontSizeAction.Mode.SMALLER));
            fontSize.add(new FontSizeAction(this, FontSizeAction.Mode.LARGER));
            view.add(fontSize);
        }
        view.add(new ToolTipOptionsAction(this));
        
        return view;
    }

    private JMenu createProofMenu() {
        JMenu proof = new JMenu("Proof");
        proof.setMnemonic(KeyEvent.VK_P);
        
        proof.add(autoModeAction);
        proof.add(new UndoLastStepAction(this, true));
        proof.add(new AbandonTaskAction(this));
        proof.addSeparator();
	proof.add(new ShowUsedContractsAction(this));
        proof.add(new ShowActiveTactletOptionsAction(this));
	proof.add(showActiveSettingsAction);
        proof.add(new ShowProofStatistics(this));
        proof.add(new ShowKnownTypesAction(this));
        
        return proof;
    }

    private JMenu createOptionsMenu() {
	JMenu options = new JMenu("Options");
	options.setMnemonic(KeyEvent.VK_O);
	
	options.add(new TacletOptionsAction(this));
	options.add(new SMTOptionsAction(this));
	options.add(setupSpeclangMenu());
	options.addSeparator();
        options.add(new JCheckBoxMenuItem(new MinimizeInteraction(this)));
        options.add(new JCheckBoxMenuItem(oneStepSimplAction));
        
        return options;
        
//	// dnd direction sensitive		
//        final boolean dndDirectionSensitivity = 
//            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isDndDirectionSensitive();
//        final JMenuItem dndDirectionSensitivityOption =
//            new JCheckBoxMenuItem("DnD Direction Sensitive", dndDirectionSensitivity);
//        dndDirectionSensitivityOption.addActionListener(new ActionListener() {
//            public void actionPerformed(ActionEvent e) {
//                boolean b = ((JCheckBoxMenuItem)e.getSource()).isSelected();           
//                ProofSettings.DEFAULT_SETTINGS.
//                getGeneralSettings().setDnDDirectionSensitivity(b);           
//        }});
//        registerAtMenu(options, dndDirectionSensitivityOption);
        
    }
    

    private JMenu createDebugMenu() {
        JMenu debug = new JMenu("Debug");
        debug.setMnemonic(KeyEvent.VK_D);
        // please note: this is doubled in proof menu
        debug.add(showActiveSettingsAction);
        return debug;
    }

    private JMenu createHelpMenu() {
        JMenu help = new JMenu("About");
        help.setMnemonic(KeyEvent.VK_A);
        
        help.add(new AboutAction(this));
        help.add(new LicenseAction(this));
        return help;
    }

    /**
     * update the selection menu for Decisionprocedures.
     * Remove those, that are not installed anymore, add those, that got installed.
     */
    public void updateSMTSelectMenu() {

	Collection<SolverTypeCollection> solverUnions = ProofIndependentSettings.DEFAULT_INSTANCE.
	                                  getSMTSettings().getUsableSolverUnions();

	if(solverUnions == null || solverUnions.isEmpty()){
	    updateDPSelectionMenu();
	}else{
	    updateDPSelectionMenu(solverUnions);
	}
	


    }
    
    private void updateDPSelectionMenu(){
	       smtComponent.setItems(null);
	   }
	   
	   private SMTInvokeAction findAction(SMTInvokeAction [] actions, SolverTypeCollection union){
	       for(SMTInvokeAction action : actions){
		   if(action.solverUnion.equals(union)){
		       return action;
		   }
	       }
	       return null;
	   }
	   
	   private void updateDPSelectionMenu(Collection<SolverTypeCollection> unions){
		SMTInvokeAction actions[] = new SMTInvokeAction[unions.size()];
	        
		int i=0; 
		for(SolverTypeCollection union : unions){
		    
		    actions[i] = new SMTInvokeAction(union);
		    i++;
		}
		
		smtComponent.setItems(actions);
	            	
		SolverTypeCollection active = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().computeActiveSolverUnion();
		 
		SMTInvokeAction activeAction = findAction(actions, active);
		
		boolean found = activeAction != null;
		if(!found){
		    Object item = smtComponent.getTopItem();
		    if(item instanceof SMTInvokeAction){
			active = ((SMTInvokeAction)item).solverUnion;
			ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().setActiveSolverUnion(active);
		    }else{
			activeAction = null;
		    }

		}
		smtComponent.setSelectedItem(activeAction); 
	   }
    
    JCheckBoxMenuItem saveSMTFile;
//    private JCheckBoxMenuItem waitForAllProvers;
    
    private JMenuItem setupSpeclangMenu() {
        JMenu result = new JMenu("Specification Parser");       
        ButtonGroup group = new ButtonGroup();
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
                
        JRadioButtonMenuItem jmlButton 
            = new JRadioButtonMenuItem("Source File Comments Are JML", gs.useJML());
        result.add(jmlButton);
        group.add(jmlButton);
        jmlButton.setIcon(IconFactory.jmlLogo(15));
        jmlButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                GeneralSettings gs 
                    = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
                gs.setUseJML(true);
                gs.setUseOCL(false);
            }
        });
        
        JRadioButtonMenuItem noneButton 
        	= new JRadioButtonMenuItem("Source File Comments Are Ignored", !gs.useJML() && !gs.useOCL());
        result.add(noneButton);
        group.add(noneButton);
        noneButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
        	GeneralSettings gs 
        	= ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        	gs.setUseJML(false);
        	gs.setUseOCL(false);
            }
    });
        
        
        return result;
    }
    
    public ProofTreeView getProofView(){
        return proofTreeView;
    }
    
//    /**
//     * returns the toolbar
//     */
//    public JToolBar getToolBar() {
//        return toolBar;
//    }
    
    /**
     * Sets the content of the current goal view. Do not use this method from outside, take method
     * {@link #updateGoalView(String, JComponent)} instead (thread safe)
     */
    private void paintGoalView(String borderTitle, JComponent goalViewPane) {
        JViewport vp = goalView.getViewport();
        if(vp!=null){
            vp.removeAll();
        }
        goalView.setViewportView(goalViewPane);
        goalView.setBorder(new TitledBorder(borderTitle));
        goalView.setBackground(goalViewPane.getBackground());
        goalView.validate();
        validate();
    }
    
    /**
     * updates the view of the sequent being displayed in the main frame
     */
    private synchronized void updateGoalView(final String borderTitle, final JComponent goalViewPane) {
        if (SwingUtilities.isEventDispatchThread()) {
            paintGoalView(borderTitle, goalViewPane);
        } else {
            Runnable sequentUpdater = new Runnable() {
                public void run() {
                    paintGoalView(borderTitle, goalViewPane);
                }
            };
            SwingUtilities.invokeLater(sequentUpdater);
        }
    }
    
    
    /**
     * prints the content of the sequent view
     */
    private void printSequentView(Sequent sequent) {
        SequentPrintFilter filter = new IdentitySequentPrintFilter ( sequent );
        final LogicPrinter printer = new LogicPrinter
        (new ProgramPrinter(null), 
                getMediator().getNotationInfo(),
                mediator.getServices());
                
        sequentView.setPrinter(printer, filter, null);
        sequentView.printSequent();
        
        updateGoalView("Current Goal", sequentView);
    }
    
    
    /** saves a proof */
    private void saveProof() {
        final KeYFileChooser jFC = GuiUtilities.getFileChooser("Choose filename to save proof");
        final String defaultName 
        	= MiscTools.toValidFileName(mediator.getSelectedProof()
        		                            .name()
        		                            .toString()).toString();
        boolean saved = jFC.showSaveDialog(this, defaultName + ".proof");
        if (saved) {
            saveProof(jFC.getSelectedFile());
        }
    }
    
    private void saveProof(String proofFile) {
        saveProof(new File(proofFile));
    }
    
    public void saveProof(File proofFile) {
        String filename = proofFile.getAbsolutePath();    
        ProofSaver saver = new ProofSaver(getMediator().getSelectedProof(), filename, Main.INTERNAL_VERSION);
        String errorMsg ;
        
        try {
            errorMsg = saver.save();
        } catch(IOException e){
            errorMsg = e.toString();              
        }
        
        if (errorMsg != null) {
            notify(new GeneralFailureEvent
                    ("Saving Proof failed.\n Error: " + errorMsg));
        }
    }
    
    public void loadProblem(File file) {
        recentFiles.addRecentFile(file.getAbsolutePath());
        final ProblemLoader pl = 
            new ProblemLoader(file, this);
        pl.addTaskListener(getUserInterface());
        pl.run();
    }
    
    private void closeTask() {
	final Proof proof = mediator.getProof();
	if (proof != null) {
	    final TaskTreeNode rootTask = proof.getBasicTask().getRootTask();
	    closeTask(rootTask); 
	}
    }

    private void closeTask(TaskTreeNode rootTask) {
       if(proofList.removeTask(rootTask)){
            for(Proof proof:rootTask.allProofs()){
                //In a previous revision the following statement was performed only
                //on one proof object, namely on: mediator.getProof()
                proof.getServices().getSpecificationRepository().removeProof(proof);
                proof.mgt().removeProofListener();
            }
            proofTreeView.removeProofs(rootTask.allProofs());
       }
    }

    // FIXME DOES NOT DO THE SAME AS THE ONE ONE ABOVE
    @Deprecated
    public void closeTaskWithoutInteraction() {
        final Proof proof = mediator.getProof();
        if (proof != null) {
            final TaskTreeNode rootTask = 
                proof.getBasicTask().getRootTask();     
            proofList.removeTaskWithoutInteraction(rootTask);   
            proof.getServices().getSpecificationRepository().removeProof(proof);
            proof.mgt().removeProofListener();
            proofTreeView.removeProofs(rootTask.allProofs());
        }
    }
    
    /**
     * brings window in front and request focus
     */
    private void popup() {
        setState(Frame.NORMAL);
        setVisible(true);
        requestFocus();
    }
    
    public void addProblem(final de.uka.ilkd.key.proof.ProofAggregate plist) {
        Runnable guiUpdater = new Runnable() {
            public void run() {
                disableCurrentGoalView = true;
                addToProofList(plist);
                setUpNewProof(plist.getFirstProof());
                disableCurrentGoalView = false;
                setProofNodeDisplay();
                popup();
            }
        };

        GuiUtilities.invokeAndWait(guiUpdater);
    }
    
    private Proof setUpNewProof(Proof proof) {
        getMediator().setProof(proof);
        return proof;
    }
    

    
    /**
     * The progress monitor that displays a progress bar in a corner of the main window.
     */
//    class MainProgressMonitor implements ProgressMonitor {
//	public void setProgress(final int progress) {
//	    KeYMediator.invokeOnEventQueue(new Runnable() {
//		public void run() {
//		    statusLine.setProgress(progress);
//		}
//	    });
//	}
//        
//        public void setMaximum(int maximum) {
//            statusLine.setProgressBarMaximum(maximum);
//        }
//    }
    
    /** invoked if a frame that wants modal access is opened */
    class MainGUIListener implements GUIListener {
        
        private void enableMenuBar(JMenuBar m, boolean b) {
            for (int i = 0; i < m.getMenuCount(); i++) {
                JMenu menu = m.getMenu(i);
		if (menu != null) { 
		    // otherwise it is a spacer
                    menu.setEnabled(b);
                }
            }
        }
        
        private Set<Component> doNotReenable;
        
	private void setToolBarDisabled() {
	    
	    assert EventQueue.isDispatchThread() : "toolbar disabled from wrong thread";
	    assert doNotReenable == null : "toolbar disabled w/o prior enable";
	    
	    doNotReenable = new HashSet<Component>();
	    Component[] cs = controlToolBar.getComponents();
	    for (int i = 0; i < cs.length; i++) {
		if (!cs[i].isEnabled()) {
		    doNotReenable.add(cs[i]);
		}
		cs[i].setEnabled(false);
	    }
	    cs = fileOpToolBar.getComponents();
	    for (int i = 0; i < cs.length; i++) {
		if (!cs[i].isEnabled()) {
		    doNotReenable.add(cs[i]);
		}
		cs[i].setEnabled(false);
	    }
	}
        
        private void setToolBarEnabled() {
            
            assert EventQueue.isDispatchThread() : "toolbar enabled from wrong thread";
            assert doNotReenable != null : "toolbar enabled w/o prior disable";
            
            Component[] cs = controlToolBar.getComponents();
            for (int i = 0; i < cs.length; i++) {
                if (!doNotReenable.contains(cs[i])) {
                    cs[i].setEnabled(true);
                }
            }
            cs = fileOpToolBar.getComponents();
            for (int i = 0; i < cs.length; i++) {
        	if (!doNotReenable.contains(cs[i])) {
                    cs[i].setEnabled(true);
                }
            }
            
            doNotReenable = null;
        }
        
        public void modalDialogOpened(GUIEvent e) {
            
            if (e.getSource() instanceof ApplyTacletDialog) {
                // disable all elements except the sequent window (drag'n'drop !) ...
                enableMenuBar(MainWindow.this.getJMenuBar(), false);
                MainWindow.this.goalView.setEnabled(false);
                MainWindow.this.proofTreeView.setEnabled(false);
                MainWindow.this.openGoalsView.setEnabled(false);
                MainWindow.this.strategySelectionView.setEnabled(false);
                MainWindow.this.ruleView.setEnabled(false);
                setToolBarDisabled();
            } else {
                // disable the whole main window ...
                MainWindow.this.setEnabled(false);
            }
        }
        
        /** invoked if a frame that wants modal access is closed */
        public void modalDialogClosed(GUIEvent e) {
            if (e.getSource() instanceof ApplyTacletDialog) {
                // enable all previously diabled elements ...
                enableMenuBar(MainWindow.this.getJMenuBar(), true);
                MainWindow.this.goalView.setEnabled(true);
                MainWindow.this.proofTreeView.setEnabled(true);
                MainWindow.this.openGoalsView.setEnabled(true);
                MainWindow.this.strategySelectionView.setEnabled(true);
                MainWindow.this.ruleView.setEnabled(true);
                setToolBarEnabled();
            } else {
                // enable the whole main window ...
                MainWindow.this.setEnabled(true);
            }
        }
        
        public void shutDown(GUIEvent e) {
            MainWindow.this.notify(new ExitKeYEvent());
            MainWindow.this.setVisible(false);
        }
        
    }
    
    /**
     * set to true if the view of the current goal should not be updated
     */
    private boolean disableCurrentGoalView = false;

   

    private synchronized void setProofNodeDisplay() {
        // FIXME
        if(Main.batchMode) {
            return;
        }
        if (!disableCurrentGoalView) {
            Goal goal;
            if(getMediator()!=null && getMediator().getSelectedProof()!=null){
                goal = getMediator().getSelectedGoal();
            } else{//There is no proof. Either not loaded yet or it is abandoned 
                final LogicPrinter printer = new LogicPrinter
                (new ProgramPrinter(null), null,null);
                sequentView.setPrinter(printer, null);
                return;
            }
            if ( goal != null && !goal.node ().isClosed() ){
                printSequentView(goal.sequent());
            } else {
                NonGoalInfoView innerNodeView = 
                    new NonGoalInfoView(getMediator().getSelectedNode(), 
                            getMediator());
                updateGoalView("Inner Node", innerNodeView);
            }
        }
    }
    
    class MainProofListener implements AutoModeListener, KeYSelectionListener,
    	SettingsListener {	
        
        Proof proof = null;
        
        
        /** focused node has changed */
        public synchronized void selectedNodeChanged(KeYSelectionEvent e) {
            if (getMediator().autoMode()) return;
            setProofNodeDisplay();	    
        }
        
        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */ 
        public synchronized void selectedProofChanged(KeYSelectionEvent e) {
            Debug.out("Main: initialize with new proof");
            
            if ( proof != null ) {
                proof.getSettings().getStrategySettings().removeSettingsListener ( this );
            }
            proof = e.getSource().getSelectedProof();
            if ( proof != null ) {
                proof.getSettings().getStrategySettings().addSettingsListener( this );
            }
            
            disableCurrentGoalView = false;	    
            goalView.setViewportView(null);
            
            setProofNodeDisplay();
           
            makePrettyView();
        }
        
        /**
         * invoked if automatic execution has started
         */
        public synchronized void autoModeStarted(ProofEvent e) {
            Debug.log4jWarn("Automode started", MainWindow.class.getName());
            disableCurrentGoalView = true;
            getMediator().removeKeYSelectionListener(proofListener);
            freezeExceptAutoModeButton();
        }
        
        /**
         * invoked if automatic execution has stopped
         */
        public synchronized void autoModeStopped(ProofEvent e) {
            Debug.log4jWarn("Automode stopped", MainWindow.class.getName());
            Debug.log4jDebug("From " + Debug.stackTrace(), MainWindow.class.getName());
            unfreezeExceptAutoModeButton();
            disableCurrentGoalView = false;
            setProofNodeDisplay();
            getMediator().addKeYSelectionListener(proofListener);
        }
        
        /** invoked when the strategy of a proof has been changed */
        public synchronized void settingsChanged ( GUIEvent e ) {
            if ( proof.getSettings().getStrategySettings() == (StrategySettings) e.getSource() ) {
                // updateAutoModeConfigButton();
            }         
        }
        
    }
        

    /** 
     * used when in batch mode to write out some statistic data
     * @param file the String with the filename where to write the statistic data
     * @param result the Object encapsulating informtation about the result, e.g.
     * String "Error" if an error has occurred. 
     * @param time the long giving the needed time in ms 
     * @param appliedRules the int giving the number of applied rules
     */
    private void printStatistics(String file, Object result, 
            long time, int appliedRules) {
        try {
            final FileWriter statistics = new FileWriter ( file, true );
            final PrintWriter statPrinter = new PrintWriter ( statistics );
            
            String fileName = Main.getFileNameOnStartUp();
            final int slashIndex = fileName.lastIndexOf ( "examples/" );
            if ( slashIndex >= 0 )
                fileName = fileName.substring ( slashIndex );
            
            statPrinter.print ( fileName + ", " );
            if ("Error".equals ( result ) )
                statPrinter.println ( "-1, -1" );
            else
                statPrinter.println ( "" + appliedRules + ", " + time );                
            statPrinter.close();
        } catch ( IOException e ) {}
    }

    /**
     * This mechanism is not good and will vanish.
     * @param info
     */
    @Deprecated
    public void taskFinished(TaskFinishedInfo info) {
        final MainStatusLine sl = getStatusLine();

        if (info.getSource() instanceof ApplyStrategy) {
            sl.reset();
            displayResults(info.getTime(), 
                    info.getAppliedRules(), 
                    info.getClosedGoals());                
        } else if (info.getSource() instanceof ProblemLoader) {
            if (!"".equals(info.getResult())) {
                final KeYExceptionHandler exceptionHandler = 
                    ((ProblemLoader)info.getSource()).getExceptionHandler();
                ExceptionDialog.showDialog(MainWindow.this,     
                        exceptionHandler.getExceptions());
                exceptionHandler.clear();
            } else {
                sl.reset();                    
                mediator.getNotationInfo().refresh(mediator.getServices());
            }
        } else {
            sl.reset();
        }
    }
    
    /** displays some status information */
    void displayResults ( long time, int appliedRules, int closedGoals ) {
        String message;       
        String timeString = "" + (time/1000)+"."+((time%1000)/100);        
        
        int closed = getMediator().getNrGoalsClosedByAutoMode();
        
        // display message in the status bar
        
        if ( appliedRules != 0 ) {
            message = "Strategy: Applied " + appliedRules + " rule";
            if ( appliedRules != 1 ) message += "s";
            message += " (" + timeString + " sec), ";
            message += " closed " + closedGoals + " goal";
            if ( closed != 1 ) message += "s";             
            message += ", " + displayedOpenGoalNumber ();
            message += " remaining"; 
            setStatusLine ( message );
        }                              
    }
    
    void displayResults(String message){
            setStatusLine(message);
    }
    
//    /**
//     * called when the batch mode has been finished 
//     * @param result the Object encapsulating informtation about the result, e.g.
//     * String "Error" if an error has occurred. 
//     * @param proof the Proof to which <tt>appliedRules</tt> rules have been 
//     * applied requiring <tt>time</tt> ms
//     * @param time the long giving the needed time in ms 
//     * @param appliedRules the int giving the number of applied rules
//     */
//    private void finishedBatchMode (Object result, 
//            Proof proof, long time, int appliedRules) {
//
//        if ( Main.getStatisticsFile() != null )
//            printStatistics ( Main.getStatisticsFile(), result, time, appliedRules );
//
//        if ("Error".equals ( result ) ) {
//            // Error in batchMode. Terminate with status -1.
//            System.exit ( -1 );
//        }
//
//        // Save the proof before exit.
//
//        String baseName = Main.getFileNameOnStartUp();
//        int idx = baseName.indexOf(".key");        
//        if (idx == -1) {
//            idx = baseName.indexOf(".proof");
//        }        
//        baseName = baseName.substring(0, idx==-1 ? baseName.length() : idx);
//
//        File f; 
//        int counter = 0;
//        do {           
//
//            f = new File(baseName + ".auto."+ counter +".proof");
//            counter++;
//        } while (f.exists());
//
//        MainWindow.getInstance ().saveProof ( f.getAbsolutePath() );
//        if (proof.openGoals ().size () == 0) {
//            // Says that all Proofs have succeeded
//            if (proof.getBasicTask().getStatus().getProofClosedButLemmasLeft()) {
//                // Says that the proof is closed by depends on (unproved) lemmas                
//                System.exit ( 0 ); //XXX, was: 2 
//            }
//            System.exit ( 0 ); 
//        } else {
//            // Says that there is at least one open Proof
//            System.exit ( 1 );
//        }
//    }

//    class MainTaskListenerBatchMode implements ProverTaskListener { // XXX
//        public void taskStarted(String message, int size) {
//            System.out.print(message+" ... ");
//        }
//        
//        public void setProgress(int position) {
//        }
//        
//        public void taskFinished(TaskFinishedInfo info) {
//            System.out.println("[ DONE ]");
//            if (info.getSource() instanceof ApplyStrategy) {
//                finishedBatchMode ( info.getResult(), 
//                        info.getProof(), info.getTime(), 
//                        info.getAppliedRules());
//                Debug.fail ( "Control flow should not reach this point." );
//            } else if (info.getSource() instanceof ProblemLoader) {
//                if (!"".equals(info.getResult())) {
//                        System.exit(-1);
//                } 
//                if(info.getProof().openGoals().size()==0) {
//                    System.out.println("proof.openGoals.size=" + 
//                            info.getProof().openGoals().size());              
//                    System.exit(0);
//                }
//                mediator.startAutoMode();
//            }
//        }
//    }
    
//    class MainTaskListener implements ProverTaskListener { // XXX
//        public void taskStarted(String message, int size) {
//            final MainStatusLine sl = getStatusLine();
//            sl.reset();
//            if (size > 0) {
//                sl.setProgressPanelVisible(true);
//                getStatusLine().setProgressBarMaximum(size);
//            }
//            sl.setStatusText(message);
//        }
//        
//        public void setProgress(int position) {
//            getStatusLine().setProgress(position);
//        }
//        
//        public void taskFinished(TaskFinishedInfo info) {
//            final MainStatusLine sl = getStatusLine();
//            
//            if (info.getSource() instanceof ApplyStrategy) {
//        	sl.reset();
//                displayResults(info.getTime(), 
//                	       info.getAppliedRules(), 
//                	       info.getClosedGoals());                
//            } else if (info.getSource() instanceof ProblemLoader) {
//                if (!"".equals(info.getResult())) {
//                    final KeYExceptionHandler exceptionHandler = 
//                        ((ProblemLoader)info.getSource()).getExceptionHandler();
//                            new ExceptionDialog(MainWindow.this,     
//                                    exceptionHandler.getExceptions());
//                            exceptionHandler.clear();
//                } else {
//                    sl.reset();                    
//                    mediator.getNotationInfo().refresh(mediator.getServices());
//                }
//            } else {
//        	sl.reset();
//            }
//        }
//    }
    
    
    
    /** Glass pane that only delivers events for the status line (i.e. the abort button)
     * 
     * This has been partly taken from the GlassPaneDemo of the Java Tutorial 
     */
    private static class BlockingGlassPane extends JComponent {
        GlassPaneListener listener;
        
        public BlockingGlassPane(Container contentPane) {
            setCursor(new Cursor(Cursor.WAIT_CURSOR));
            
            listener = new GlassPaneListener(this, contentPane);
            addMouseListener(listener);
            addMouseMotionListener(listener);
        }
    }
    
    /**
     * Mouse listener for the glass pane that only delivers events for the status line (i.e. the
     * abort button)
     * 
     * This has been partly taken from the GlassPaneDemo of the Java Tutorial
     */
    private static class GlassPaneListener extends MouseInputAdapter {
        Component currentComponent = null;
        Component glassPane;
        Container contentPane;
        
        public GlassPaneListener ( Component glassPane,
                Container contentPane ) {
            this.glassPane     = glassPane;
            this.contentPane   = contentPane;
        }
        
        public void mouseMoved(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        /*
         * We must forward at least the mouse drags that started with mouse presses over the check box.
         * Otherwise, when the user presses the check box then drags off, the check box isn't disarmed --
         * it keeps its dark gray background or whatever its L&F uses to indicate that the button is
         * currently being pressed.
         */
        public void mouseDragged(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        public void mouseClicked(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        public void mouseEntered(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        public void mouseExited(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        public void mousePressed(MouseEvent e) {
            redispatchMouseEvent(e);
        }
        
        public void mouseReleased(MouseEvent e) {
            redispatchMouseEvent(e);
            currentComponent = null;
        }
        
        private void redispatchMouseEvent(MouseEvent e) {
            if ( currentComponent != null ) {
                dispatchForCurrentComponent ( e );
            } else {
                int       eventID        = e.getID();
                Point     glassPanePoint = e.getPoint();
                
                Point     containerPoint =
                    SwingUtilities.convertPoint(glassPane,
                            glassPanePoint, 
                            contentPane);
                Component component      =
                    SwingUtilities.getDeepestComponentAt(contentPane,
                            containerPoint.x,
                            containerPoint.y);
                
                if ( eventID == MouseEvent.MOUSE_PRESSED &&
                        isLiveComponent ( component ) ) {
                    currentComponent = component;
                    dispatchForCurrentComponent ( e );		
                }
            }
        }
        
        // FIXME This is not really good.
        private boolean isLiveComponent ( Component c ) {
            // this is not the most elegant way to identify the right
            // components, but it scales well ;-)
            while ( c != null ) {
                if ( (c instanceof JComponent) && 
                        AUTO_MODE_TEXT.equals(((JComponent)c).getToolTipText()) ) 
                    return true;
                c = c.getParent ();
            }
            return false;
        }
        
        private void dispatchForCurrentComponent ( MouseEvent e ) {
            Point glassPanePoint = e.getPoint();
            Point componentPoint =
                SwingUtilities.convertPoint( glassPane,
                        glassPanePoint, 
                        currentComponent );
            currentComponent.dispatchEvent(new MouseEvent(currentComponent,
                    e.getID(),
                    e.getWhen(),
                    e.getModifiers(),
                    componentPoint.x,
                    componentPoint.y,
                    e.getClickCount(),
                    e.isPopupTrigger()));
        }
    }
    
    
    private final class DPEnableControl implements KeYSelectionListener{

	private void enable(boolean b){
	    smtComponent.setEnabled(b);
	}

        public void selectedProofChanged(KeYSelectionEvent e) {
            
	    if(e.getSource().getSelectedProof() != null){
              	  enable(!e.getSource().getSelectedProof().closed());
	       }else{
		   enable(false);
	       }
    	
        }
        
        public void selectedNodeChanged(KeYSelectionEvent e) {
            selectedProofChanged(e);
    	
        }
	
    }
    
    
    /**
     * This action is responsible for the invocation of an SMT solver
     * For example the toolbar button is paramtrized with an instance of this action
     */
    private final class SMTInvokeAction extends AbstractAction {
	SolverTypeCollection solverUnion;
	
	public SMTInvokeAction(SolverTypeCollection solverUnion) {
	    this.solverUnion = solverUnion;
	    if (solverUnion != SolverTypeCollection.EMPTY_COLLECTION) {
		putValue(SHORT_DESCRIPTION, "Invokes " + solverUnion.toString());
	    } 
	}
	
	public boolean isEnabled() {
	    boolean b = super.isEnabled() && solverUnion != SolverTypeCollection.EMPTY_COLLECTION && 
 	      mediator != null && mediator.getSelectedProof() != null && !mediator.getSelectedProof().closed();
	    return b;
	}
	  
	public void actionPerformed(ActionEvent e) {
	    if (!mediator.ensureProofLoaded() || solverUnion ==SolverTypeCollection.EMPTY_COLLECTION){
		return;
	    }
	    final Proof proof = mediator.getProof();
	  
	    Thread thread = new Thread(new Runnable() {	        
	        @Override
	        public void run() {
	        
	  
	            SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
	                            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),proof);
	            SolverLauncher launcher = new SolverLauncher(settings);
	            launcher.addListener(new SolverListener(settings));
	            launcher.launch(solverUnion.getTypes(),
			            SMTProblem.createSMTProblems(proof),
			            proof.getServices());
	  
	        }
	    });
	    thread.start();
	    
	
	    

	}
	
	public String toString(){
	    return solverUnion.toString();
	}

	@Override
	public boolean equals(Object obj) {
	    if(!(obj instanceof SMTInvokeAction)){
		return false;
	    }
	    
	    return this.solverUnion.equals(((SMTInvokeAction)obj).solverUnion);
	}
    }
    
    public void loadCommandLineFile() {
        if (Main.getFileNameOnStartUp() != null) {
            loadProblem(new File(Main.getFileNameOnStartUp()));
        } else if(Main.getExamplesDir() != null) {
            openExampleAction.actionPerformed(null);
        }
    }
    
    /**
     * informs the NotificationManager about an event
     * 
     * @param event
     *            the NotificationEvent
     */
    public void notify(NotificationEvent event) {
        if (notificationManager != null) {
            notificationManager.notify(event);
        }
    }
    

    public static boolean hasInstance() {
        return instance != null;
    }   
    
    
    /**
     * returns an instance of Main and creates one if necessary
     * <strong>Do not use</strong> this method to access the mediator as long as
     * you do not attempt create a GUI element. In particular be aware that the 
     * pattern <tt>getInstance().mediator().getProof()</tt> breaks GUI and prover 
     * separation and will not work if an alternative GUI is used (e.g. soon for 
     * the visual debugger). 
     * 
     * Further the above pattern is very fragile as the mediator may have changed 
     * the selected proof. Usually if you want to have access to a proof e.g. in
     * the strategy hand the proof object over at the creation time of the component.
     * 
     * @return the instance of Main
     * @throws IllegalStateException 
     */
    public static MainWindow getInstance() throws IllegalStateException {
        return getInstance(true);
    }

    /**
     * returns an instance of Main and creates one if necessary
     * <strong>Do not use</strong> this method to access the mediator as long as
     * you do not attempt create a GUI element. In particular be aware that the 
     * pattern <tt>getInstance(boolean).mediator().getProof()</tt> breaks GUI and prover 
     * separation and will not work if an alternative GUI is used (e.g. soon for 
     * the visual debugger). 
     * 
     * Further the above pattern is very fragile as the mediator may have changed 
     * the selected proof. Usually if you want to have access to a proof e.g. in
     * the strategy hand the proof object over at the creation time of the component.
     * 
     * @param visible a boolean indicating if Main shall be made visible
     * @return the instance of Main
     * @throws Exception 
     */
    public static MainWindow getInstance(final boolean visible) throws IllegalStateException {
        
        if(instance == null) {
            // TODO Come up with a better exception class
            throw new IllegalStateException("There is no GUI main window. Sorry.");
        }
        
        // in a getter method the state ought not be changed. -> Lead to trouble.
//        if(visible && !instance.isVisible()) {
//            GuiUtilities.invokeOnEventQueue(new Runnable() {
//                public void run() {                            
//                    instance.setVisible(true);
//                }
//            });
//        }
        
        return instance;
    }

    public static void createInstance(String title) {
	assert instance == null : "Attempt to create a second mainwindow";
	if(instance == null) {
	    instance = new MainWindow();
	    instance.initialize(title);
	}
    }

    public static void setVisibleMode(boolean visible) {
	MainWindow.visible = visible;
    }

    public TaskTree getProofList() {
	return proofList;
    }

    public RecentFileMenu getRecentFiles() {
	return recentFiles;
    }

    public UserInterface getUserInterface() {
        return userInterface;
    }
    
    /**
     * @return the autoModeAction
     */
    public Action getAutoModeAction() {
        return autoModeAction;
    }

    public Action getOpenMostRecentFileAction() {
        return openMostRecentFileAction;
    }

    public void savePreferences() {
        try {
            prefSaver.save(this);
        } catch (BackingStoreException e) {
            // it is not tragic if the preferences cannot be stored.
            e.printStackTrace();
        }
    }

}