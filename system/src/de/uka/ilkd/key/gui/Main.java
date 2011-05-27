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
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Cursor;
import java.awt.Desktop;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.GridBagLayout;
import java.awt.Point;
import java.awt.TextArea;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.ButtonGroup;
import javax.swing.Icon;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
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
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.gui.configuration.ViewSelector;
import de.uka.ilkd.key.gui.lemmatagenerator.FileChooser;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataHandler;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.ExitKeYEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.smt.ComplexButton;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SettingsDialog;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.gui.smt.TemporarySettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.PreferenceSaver;
import de.uka.ilkd.key.util.ProgressMonitor;
import java.awt.GraphicsEnvironment;
import java.util.List;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;


public final class Main extends JFrame implements IMain {

    public static final String INTERNAL_VERSION = 
	KeYResourceManager.getManager().getSHA1();

    private static final String VERSION = 
	KeYResourceManager.getManager().getVersion() + 
	" (internal: "+INTERNAL_VERSION+")";

    private static final String COPYRIGHT="(C) Copyright 2001-2011 "
        +"Universit\u00e4t Karlsruhe, Universit\u00e4t Koblenz-Landau, "
        +"and Chalmers University of Technology";
    
    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;
    
    /** size of the tool bar icons */
    private static final int TOOLBAR_ICON_SIZE = 15;
    
    /** the tab bar at the left */
    private JTabbedPane tabbedPane;
    
    /** the toolbar */
    private JToolBar toolBar;
    
    /** the current goal view */
    private JScrollPane goalView;

    /** the current proof tree*/
    private JPanel proofView;

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
    protected KeYMediator mediator;
    
    /** the status line */
    MainStatusLine statusLine;
    
    /** the main progress monitor */
    protected ProgressMonitor progressMonitor = new MainProgressMonitor();
    
    /** listener to global proof events */
    private MainProofListener proofListener;
    
    /** listener to gui events */
    private MainGUIListener guiListener;
    private RecentFileMenu recentFiles;
    
    private boolean frozen = false;
   
    private static KeYFileChooser fileChooser = null;
    
    private PreferenceSaver prefSaver =
        new PreferenceSaver(Preferences.userNodeForPackage(Main.class));
    
    private static final String PARA = 

       "<p style=\"font-family: lucida;font-size: 12pt;font-weight: bold\">";
       
    /** button for starting and stopping automatic mode */
    public static AutoModeAction autoModeAction;
    
    /** action for opening a KeY file */
    public static OpenFile openFileAction;
    
    /** action for opening an example */
    public static OpenExample openExampleAction;    
    
    /** action for opening the most recent KeY file */
    public static OpenMostRecentFile openMostRecentFileAction;
    
    /** action for editing the most recent KeY file */
    public static EditMostRecentFile editMostRecentFileAction;    
    
    /** action for saving a proof (attempt) */
    public static SaveFile saveFileAction;
    
    /** action for opening the proof management dialog */
    public static ProofManagementAction proofManagementAction;
    
    public static LoadUserDefinedTacletsAction loadUserDefinedTacletsAction;
    

    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";

    /** if true then automatically start startAutoMode after the key-file is loaded*/
    public static boolean batchMode = false;
    
    /** Determines if the KeY prover is started in visible mode*/
    public static boolean visible = true;

    public static String statisticsFile = null;

    private static String examplesDir = null;
    
    
    /** external prover GUI elements */
    private SMTSettingsListener smtSettingsListener;
    
    protected static String fileNameOnStartUp = null;
    
    /** for locking of threads waiting for the prover to exit */
    public Object monitor = new Object();
    
    private static final String TACLET_OPTIONS_MENU_STRING = "ToolTip options ";
    
    public static Main instance = null;    
    
    private ProverTaskListener taskListener;
    
    private NotificationManager notificationManager;

    private ComplexButton smtComponent;
    
    /** The menu for the SMT solver options */
    public final JMenu smtOptions = new JMenu("SMT Solvers...");
    
    
    private final ProblemInitializerListener piListener = new ProblemInitializerListener(){

	    @Override
        public void progressStarted(Object sender) {
		 mediator().stopInterface(true);
            
        }

	    @Override
        public void progressStopped(Object sender) {
		 mediator().startInterface(true);
            
        }

	    @Override
        public void proofCreated(ProblemInitializer sender,
                ProofAggregate proofAggregate) {
		addProblem(proofAggregate);
		resetStatus(sender);
        }
	    
	    @Override
	    public void resetStatus(Object sender) {
		setStandardStatusLine();
	    }

	    @Override
        public void reportStatus(Object sender,
                String status, int progressMax) {
		setStatusLine(status, progressMax);
            
        }

	    @Override
        public void reportStatus(Object sender,
                String status) {
		setStatusLine(status);
            
        }

	    @Override
        public void reportException(Object sender,
                ProofOblInput input, Exception e) {
		reportStatus(sender,input.name() + " failed");
            
        }
    };
    
    /**
     * creates prover -- private, use getInstance()
     * 
     * @param title
     *            the String containing the frame's title
     */
    protected Main(String title) {
        super(title);
        setIconImage(IconFactory.keyLogo());
        setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        proofListener = new MainProofListener();
        guiListener = new MainGUIListener();
        
        taskListener = (Main.batchMode ? (ProverTaskListener)
                new MainTaskListenerBatchMode() : 
            (ProverTaskListener) new MainTaskListener());
        
        setMediator(new KeYMediator(this));
        
        initNotification();
        initProofList();
        layoutMain();
        initGoalList();
        initGUIProofTree();
        
        SwingUtilities.updateComponentTreeUI(this);
        ToolTipManager.sharedInstance().setDismissDelay(30000);
        addWindowListener(new MainListener());
        
    }
    
    private void initNotification() {
        if (!batchMode) {
            notificationManager = new NotificationManager(mediator);
        }
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
     */
    public static Main getInstance() {
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
     */
    public static Main getInstance(final boolean visible) {
        if (instance == null) {
            instance = new Main("KeY " + KeYResourceManager.getManager().getVersion());
        }
        if (!instance.isVisible()) {
            if (SwingUtilities.isEventDispatchThread()) {
                instance.setVisible(visible); // XXX: enough?
            } else {
                SwingUtilities.invokeLater(new Runnable() {
                    public void run() {                            
                        if (!instance.isVisible())
                            instance.setVisible(visible);
                    }
                });
            }
        }
        return instance;
    }
    
    
    public String getInternalVersion() {
        return INTERNAL_VERSION;
    }
    
    public void updateUI() {
        if (goalView != null)
            goalView.updateUI();
        if (proofView != null)
            proofView.updateUI();
        if (openGoalsView != null)
            openGoalsView.updateUI();
        if (ruleView != null)
            ruleView.updateUI();
        if (proofListView != null)
            proofListView.updateUI();
    }
    
    public ProblemInitializer createProblemInitializer(){
	ProblemInitializer pi = new ProblemInitializer(getProgressMonitor(),
		mediator().getProfile(), new Services(mediator().getExceptionHandler()),true,piListener);
	return pi;
    }
    
    /**
     * sets the mediator to corresspond with other gui elements
     * 
     * @param m
     *            the KeYMediator
     */
    private void setMediator(KeYMediator m) {
        if (mediator != null)
            unregister();
        mediator = m;
        
        // The following needs to be called before the SequentView
        // is created.
        Config.DEFAULT.setDefaultFonts();
        sequentView = new SequentView(mediator);
        register();
    }
    
    /** register several listeners */
    private void register() {
        mediator.addKeYSelectionListener(proofListener);
        mediator.addAutoModeListener(proofListener);
        mediator.addGUIListener(guiListener);
    }
    
    /** unregister several listeners */
    private void unregister() {
        mediator.removeKeYSelectionListener(proofListener);
        mediator.removeAutoModeListener(proofListener);
        mediator.removeGUIListener(guiListener);
    }
    
    /**
     * return the mediator
     * 
     * @return the mediator
     */
    public KeYMediator mediator() {
        return instance.mediator;
    }
    
    public void setVisible(boolean v){
        super.setVisible(v && visible);
    }
    
    /** paints empty view */
    private void paintEmptyViewComponent(JComponent pane, String name) { 	
	pane.setBorder(new TitledBorder(name));
	pane.setBackground(Color.white);
	if (pane instanceof JScrollPane) {
	    ((JScrollPane) pane).getViewport().setBackground(Color.white);
        }
	pane.setMinimumSize(new java.awt.Dimension(150,0));
    }
    
    /** adds a new tab */
    public void addTab(String tabname, JComponent view, String description) {
	tabbedPane.addTab(tabname, null, view, description);
    }
    
    /** sets the tool bar */
    private void setToolBar(JToolBar bar) {
        toolBar = bar;
        toolBar.setFloatable(true);
        toolBar.setRollover(true);
    }
    
    /** lays out the main frame */
    protected void layoutMain() {
        // set overall layout manager
        getContentPane().setLayout(new BorderLayout());
        
        // create empty components first
        setJMenuBar(new JMenuBar());
        setToolBar(new JToolBar("Proof Control"));
        
        autoModeAction            = new AutoModeAction();
        openFileAction            = new OpenFile();
        openExampleAction         = new OpenExample();
        openMostRecentFileAction  = new OpenMostRecentFile();
        editMostRecentFileAction  = new EditMostRecentFile();
        saveFileAction            = new SaveFile();
        proofManagementAction     = new ProofManagementAction();
        loadUserDefinedTacletsAction = new LoadUserDefinedTacletsAction();

	// ============================================================
	// ==================  create empty views =====================
	// ============================================================
	
	goalView = new JScrollPane();	
	paintEmptyViewComponent(goalView, "Current Goal");	

	proofView = new JPanel();
        proofView.setLayout(new BorderLayout(0,0));
       
	paintEmptyViewComponent(proofView, "Proof");

	openGoalsView = new JScrollPane();
	paintEmptyViewComponent(openGoalsView, "Open Goals");

	strategySelectionView = new StrategySelectionView();
	if ( mediator != null ) {
	    strategySelectionView.setMediator(mediator);
	}

	ruleView = new RuleView ();
	if ( mediator != null ) {
	    ruleView.setMediator(mediator);
	}

	// MENU BAR
	// ============================================================
	// ==================  create menu bar entries ================
	// ============================================================
	createMenuBarEntries();

	// TOOL BAR SECTION 
	// ============================================================
	// ==================== create tool bar entries ===============
	// ============================================================

	toolBar.add(createAutoModeButton());
        toolBar.addSeparator();                        
        toolBar.addSeparator();
        toolBar.addSeparator();
        ComplexButton comp = createSMTComponent();
        toolBar.add(comp.getActionComponent());
        toolBar.add(comp.getSelectionComponent());

        

        toolBar.addSeparator();

        
        
        final JButton goalBackButton = new JButton();
        goalBackButton.setAction(new UndoLastStep(false));
        
        toolBar.add(goalBackButton);
        toolBar.addSeparator();
                       
        JToolBar fileOperations = new JToolBar("File Operations");        
        fileOperations.add(createOpenFile());
        fileOperations.add(createOpenMostRecentFile());
        fileOperations.add(createEditMostRecentFile());
        fileOperations.add(createSaveFile());        
        fileOperations.addSeparator();
        fileOperations.add(createProofManagementComponent());
        
        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_C, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()), 
        "copy");
        goalView.getActionMap().put("copy", new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                copyHighlightToClipboard(sequentView);
            }
        });
        
        JPanel toolBarPanel = new JPanel();
        toolBarPanel.setLayout(new FlowLayout(FlowLayout.LEADING));
        toolBarPanel.add(toolBar);
        toolBarPanel.add(fileOperations);
        
        getContentPane().add(getClipBoardArea(), BorderLayout.PAGE_START);
        getContentPane().add(toolBarPanel, BorderLayout.PAGE_START);
        
        // ============================================================
        // ==================== create tabbed pane ====================
        // ============================================================
        
        tabbedPane = new JTabbedPane();
        
        addTab("Proof", proofView, "The current state of the " + "proof as tree");
        
        addTab("Goals", openGoalsView, "The currently open goals");
        
        tabbedPane.addTab("Proof Search Strategy", null, strategySelectionView,
        "Select strategy for automated proof search");
        
        tabbedPane.addTab("Rules", null, new JScrollPane(ruleView), "All available rules");
        tabbedPane.setName("leftTabbed");
        tabbedPane.setSelectedIndex(0);
        tabbedPane.setPreferredSize(new java.awt.Dimension(250, 440));
        tabbedPane.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        tabbedPane.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        
        proofListView.setPreferredSize(new java.awt.Dimension(250, 100));
        paintEmptyViewComponent(proofListView, "Proofs");
        
        JSplitPane leftPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, proofListView, tabbedPane) {
            public void setUI(javax.swing.plaf.SplitPaneUI ui) {
                try {
                    super.setUI(ui);
                } catch (NullPointerException e) {
                    Debug.out("Exception thrown by class Main at setUI");
                }
            }
        }; // work around bug in
        // com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
        
        leftPane.setName("leftPane");
        leftPane.setOneTouchExpandable(true);
        
        JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftPane, goalView) {
            public void setUI(javax.swing.plaf.SplitPaneUI ui) {
                try {
                    super.setUI(ui);
                } catch (NullPointerException e) {
                    Debug.out("Exception thrown by class Main at setUI");
                }
            }
        }; // work around bug in
        // com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
        splitPane.setResizeWeight(0); // the right pane is more important
        splitPane.setName("splitPane");
        splitPane.setOneTouchExpandable(true);
        getContentPane().add(splitPane, BorderLayout.CENTER);
        
        statusLine = new MainStatusLine("<html>" + PARA + COPYRIGHT + PARA
                + "KeY is free software and comes with ABSOLUTELY NO WARRANTY."
                + " See About | License.", getFont());
        getContentPane().add(statusLine, BorderLayout.SOUTH);
        
        GraphicsEnvironment env =
            GraphicsEnvironment.getLocalGraphicsEnvironment();
        setBounds(env.getMaximumWindowBounds());
        
        prefSaver.load(this);
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
		    SMTSettings.getInstance().setActiveSolverUnion(action.solverUnion);
		}
	
	    }
	});

	updateSMTSelectMenu();
	mediator.addKeYSelectionListener(new DPEnableControl());
	return smtComponent;
    }
    
    private JComponent createAutoModeButton() {
        JButton b = new JButton(autoModeAction);
        b.putClientProperty("hideActionText", Boolean.TRUE);
        //the following rigmarole is to make the button slightly wider
        JPanel p = new JPanel();
        p.setLayout(new GridBagLayout());
        p.add(b);
        return p;    
    }
    
    private JComponent createOpenFile() {
        final JButton button = new JButton();
        button.setAction(openFileAction);
        button.setText(null);
        return button;
    }
    
    private JComponent createOpenExample() {
        final JButton button = new JButton();
        button.setAction(openExampleAction);
        button.setText(null);
        return button;
    }    
    
    private JComponent createOpenMostRecentFile() {
        final JButton button = new JButton();
        button.setAction(openMostRecentFileAction);
        button.setText(null);        
        return button;
    }
    
    private JComponent createEditMostRecentFile() {
        final JButton button = new JButton();
        button.setAction(editMostRecentFileAction);
        button.setText(null);        
        return button;	
    }    
    
    private JComponent createSaveFile() {
        final JButton button = new JButton();
        button.setAction(saveFileAction);
        button.setText(null);
        return button;
    }

    private JComponent createProofManagementComponent() {
        final JButton button = new JButton();
        button.setAction(proofManagementAction);
        button.setText("Proof Management");
        return button;
    }

    public ProverTaskListener getProverTaskListener() {
        return taskListener;
    }
    
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
        if (SwingUtilities.isEventDispatchThread())
            setStandardStatusLineImmediately();
        else {
            Runnable lineUpdater = new Runnable() {
                public void run() {
                    setStandardStatusLineImmediately();
                }
            };
            SwingUtilities.invokeLater(lineUpdater);
        }
    }
    
    private void setStatusLineImmediately(String s) {
        statusLine.reset();
        statusLine.setStatusText(s);
        statusLine.setProgressPanelVisible(false);
        statusLine.validate();
        statusLine.paintImmediately(0, 0, statusLine.getWidth(), statusLine.getHeight());
    }
    
    private void setStatusLineImmediately(String s, int totalChars) {
        statusLine.reset();
        statusLine.setStatusText(s);
        getProgressMonitor().setMaximum(totalChars);
        statusLine.setProgressPanelVisible(true);
        // statusLine.setAbortButtonEnabled(false);
        statusLine.validate();
        statusLine.paintImmediately(0, 0, statusLine.getWidth(), statusLine.getHeight());
    }
    
    /**
     * Display the given message in the status line, make progress bar and abort button visible, set
     * the progress bar range to the given value, set the current progress to zero
     */
    public void setStatusLine(String s, int totalChars) {
        if (SwingUtilities.isEventDispatchThread())
            setStatusLineImmediately(s, totalChars);
        else {
            final String str = s;
            final int max = totalChars;
            Runnable lineUpdater = new Runnable() {
                public void run() {
                    setStatusLineImmediately(str, max);
                }
            };
            SwingUtilities.invokeLater(lineUpdater);
        }
    }
    
    /**
     * Display the given message in the status line, make progress bar and abort button invisible
     */
    public void setStatusLine(String s) {
        if (SwingUtilities.isEventDispatchThread())
            setStatusLineImmediately(s);
        else {
            final String str = s;
            Runnable lineUpdater = new Runnable() {
                public void run() {
                    setStatusLineImmediately(str);
                }
            };
            SwingUtilities.invokeLater(lineUpdater);
        }
    }
    
    /**
     * Get the progress monitor that will update a progress bar in a corner of the main window.
     */
    public ProgressMonitor getProgressMonitor() {
        return progressMonitor;
    }
    
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
    
    /** exit */
    protected void exitMain() {
        boolean quit = false;       
        final int option = JOptionPane.showConfirmDialog
        (Main.this, "Really Quit?", "Exit", 
                JOptionPane.YES_NO_OPTION);		   	    
        if (option == JOptionPane.YES_OPTION) {
            quit = true;
        } 


        recentFiles.store(PathConfig.RECENT_FILES_STORAGE);

        if (quit) {            
            mediator.fireShutDown(new GUIEvent(this));

            System.out.println("Have a nice day.");
            
            try {
                prefSaver.save(this);
            } catch (BackingStoreException e) {
                e.printStackTrace();
            }
            
            System.exit(-1);
        }
        // Release threads waiting for the prover to exit
        synchronized (this.monitor) {
            this.monitor.notifyAll();
        }
    }
    
 
    /** opens selection dialog for the maximum tooltip line number */
    protected void selectMaxTooltipLines() {
        ViewSelector vselector = new ViewSelector(this);
        vselector.setVisible(true);
    }
    
    /** opens selection dialog for choices */
    protected void selectChoices() {
	new ChoiceSelector
	    (ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }
    
    protected void showActivatedChoices() {
        Proof currentProof = mediator.getProof();
        if (currentProof == null) {
            mediator
            .notify(new GeneralInformationEvent("No Options available.",
                    "If you wish to see Taclet Options "
                    + "for a proof you have to load one first"));
        } else {
            String message = "Active Taclet Options:\n";
            for (final String choice : currentProof.getSettings().
                    getChoiceSettings().getDefaultChoices().values()) {
                message += choice + "\n";
            }
            final JTextComponent activeOptions = new JTextArea(message);
            activeOptions.setEditable(false);
            JOptionPane.showMessageDialog(Main.this, activeOptions, "Active Taclet Options",
                    JOptionPane.INFORMATION_MESSAGE);
        }
    }
    
    private void showUsedContracts() {
	Proof currentProof = mediator.getProof();
        if(currentProof == null) {
            mediator.notify(new GeneralInformationEvent("No contracts available.",
                    "If you wish to see the used contracts "
                    + "for a proof you have to load one first"));
        } else {
            ProofManagementDialog.showInstance(mediator.getProof()
                    				       .env()
                    				       .getInitConfig(),
                    			       mediator.getProof());        
        }
    }
        
    
    protected void showTypeHierarchy() {
        Proof currentProof = mediator.getProof();
        if(currentProof == null) {
            mediator.notify(new GeneralInformationEvent("No Type Hierarchy available.",
                    "If you wish to see the types "
                    + "for a proof you have to load one first"));
        } else {
            final JDialog dialog = new JDialog(this, "Known types for this proof", true);
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            Container pane = dialog.getContentPane();
            pane.setLayout(new BorderLayout());
            {   
                JScrollPane scrollpane = new JScrollPane();
                ClassTree classTree = new ClassTree(false, false, currentProof.getServices());
                classTree.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
                scrollpane.setViewportView(classTree);
                pane.add(scrollpane, BorderLayout.CENTER);
            }
            {
                final JButton button = new JButton("OK");
                button.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        dialog.setVisible(false);
                        dialog.dispose();
                    }
                });
                {
                    JPanel panel = new JPanel();
                    panel.add(button);
                    pane.add(panel, BorderLayout.SOUTH);
                    dialog.getRootPane().setDefaultButton(button);
                    ActionListener escapeListener = new ActionListener() {
                	public void actionPerformed(ActionEvent event) {
                	    if(event.getActionCommand().equals("ESC")) {
                		button.doClick();
                	    }
                	}
                    };
                    button.registerKeyboardAction(
                	    escapeListener,
                	    "ESC",
                	    KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                	    JComponent.WHEN_IN_FOCUSED_WINDOW);

                }
            }
            dialog.setSize(300, 400);
            dialog.setLocationRelativeTo(this);
            dialog.setVisible(true);
        }
    }

    public void showProofManagement(){
	if(mediator.getProof() == null){
	    mediator.notify
	    (new GeneralFailureEvent("Please load a proof first"));
	}else{
	    ProofManagementDialog.showInstance(mediator.getProof().env().getInitConfig());
	}
    }

    /**
     * for debugging - opens a window with the settings from current Proof and the default settings
     */
    protected void showSettings() {
        String message;
        
        message = "Default Settings: \n" + ProofSettings.DEFAULT_SETTINGS.settingsToString()
        + "\n----------\n";
        message += "Settings[CurrentProof]:\n"
            + ((mediator.getProof() == null) ? "No proof loaded." : mediator.getProof()
                    .getSettings().settingsToString());
        
        final JTextArea settings = new JTextArea(message, 30, 80);
        settings.setEditable(false);
        settings.setLineWrap(true);
        
        JScrollPane settingsPane = new JScrollPane(settings);
        
        JOptionPane.showMessageDialog(Main.this, settingsPane, "Settings",
                JOptionPane.INFORMATION_MESSAGE);
    }
    
    private int computeInteractiveSteps(Node node) {
        int steps = 0;
        final Iterator<Node> it = node.childrenIterator();
        while (it.hasNext()) {
          steps += computeInteractiveSteps(it.next());
        }
        
        if (node.getNodeInfo().getInteractiveRuleApplication()) {
            steps++;
        }
        return steps;
    }
    
    
    protected void showStatistics() {
	final Proof proof = mediator.getSelectedProof();
        if(proof == null) {
            mediator.notify(new GeneralInformationEvent("No statistics available.",
                    "If you wish to see the statistics "
                    + "for a proof you have to load one first"));
        } else {
	    String stats = proof.statistics();

	    int interactiveSteps = computeInteractiveSteps(proof.root());                  
	    stats += "Interactive Steps: " +interactiveSteps;

	    JOptionPane.showMessageDialog(Main.this, 
		    stats,
		    "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
	}
    }
    
    protected void makePrettyView() {
        if (mediator().ensureProofLoadedSilent()) {
            mediator().getNotationInfo().refresh(mediator.getServices());
            mediator().getProof().fireProofGoalsChanged();
        }        
    }
    
    public void showLicense() {
        
        URL lic = 
            KeYResourceManager.getManager().getResourceFile(Main.class,
            "LICENSE.TXT"); 
        StringBuffer sb=new StringBuffer();
        try {
            FileInputStream inp=new FileInputStream(lic.getFile());
            while (inp.available()>0) sb.append((char)inp.read());	   
        } catch (IOException ioe) {
            System.out.println("License file cannot be loaded or is missing: \n"+
                    COPYRIGHT+"\nKeY is protected by the "
                    +"GNU General Public License");
            sb=new StringBuffer(COPYRIGHT+"\nKeY is protected by the "
                    +"GNU General Public License");
        } 
        String s=sb.toString();
        JScrollPane scroll = new JScrollPane();
        JTextArea text = new JTextArea(s,20,40);
        text.setEditable(false);
        text.setCaretPosition(0);
        scroll.setViewportView(text);
        JFrame fr = new JFrame("KeY License");
        fr.getContentPane().setLayout(new BorderLayout());
        fr.getContentPane().add(scroll,BorderLayout.CENTER);
        JButton ok = new JButton("OK");
        ok.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {		   
                ((JFrame)((JButton)e.getSource())
                        .getTopLevelAncestor()).dispose();
            }});
        fr.getContentPane().add(ok, BorderLayout.SOUTH);
        fr.setSize(600,900);
        fr.getContentPane().add(scroll);
        fr.setVisible(true);
    }
    
    public void showAbout() {
        String aspects = compiledAspects();
        JOptionPane pane =new JOptionPane(
                COPYRIGHT+"\n\nWWW: http://key-project.org\n\nVersion "+
                VERSION
                + ((aspects.length()==0) ? "":
                    "\nCompiled with Aspects:\n"+aspects)
                    ,
                    JOptionPane.INFORMATION_MESSAGE, JOptionPane.DEFAULT_OPTION,
                    IconFactory.keyLogo(105,60));
        JDialog dialog = pane.createDialog(this, "The KeY Project");
        dialog.setVisible(true);
    }
    
    
    /**
     * Return a list of aspects compiled into the system, one by line. The idea is that the aspects
     * will advise this method to add themselves to the list.
     */
    public String compiledAspects() {
        return "";
    }
    
    /**
     * registers a new menuitem at the given menu
     * 
     * @param menu
     *            the JMenu where to register the new item
     * @param item
     *            the JMenuItem to register
     */
    public void registerAtMenu(JMenu menu, JMenuItem item) {
        menu.add(item);
    }
    
    /**
     * adds a separator to the given menu
     */
    public void addSeparator(JMenu menu) {
        menu.addSeparator();
    }
    
    /** the number of goals the goal list currently contains */
    public int displayedOpenGoalNumber() {
        return goalList.getModel().getSize();
    }
    
    /** starts the goal choice frame */
    protected void initGoalList() {
        goalList = new GoalList(mediator);
        goalList.setSize(goalList.getPreferredSize());
        openGoalsView.setViewportView(goalList);
    }
    
    protected void initProofList() {
        proofList = new TaskTree(mediator);
        proofListView = new JScrollPane();
    }
    
    protected void addToProofList(de.uka.ilkd.key.proof.ProofAggregate plist) {
        proofList.addProof(plist);
        // GUI
        proofList.setSize(proofList.getPreferredSize());
        proofListView.setViewportView(proofList);
    }
    
    /** starts the gui proof tree frame */
    protected void initGUIProofTree() {
	ProofTreeView guiProofTree = new ProofTreeView(mediator);
	guiProofTree.setSize(guiProofTree.getPreferredSize());
	guiProofTree.setVisible(true);
        proofView.removeAll();
	proofView.add(guiProofTree);
    }
    
    
    
    
    private static java.awt.TextArea clipBoardTextArea;

    private static TextArea getClipBoardArea() {
	if (clipBoardTextArea == null) {
	    clipBoardTextArea = new java.awt.TextArea(
		    "",10,10,java.awt.TextArea.SCROLLBARS_NONE) {
		public java.awt.Dimension getMaximumSize() {
		    return new java.awt.Dimension(0,0);
		}
	    };
	}
	return clipBoardTextArea;
    }

 
    
    public static void copyHighlightToClipboard(SequentView view) {
        String s = view.getHighlightedText();
        // now CLIPBOARD
        java.awt.datatransfer.StringSelection ss = 
            new java.awt.datatransfer.StringSelection(s);
        final TextArea clipBoard = getClipBoardArea();
        clipBoard.getToolkit().getSystemClipboard().setContents(ss,ss);
        // now PRIMARY
        clipBoard.setText(s);
        clipBoard.selectAll();
    }
    
    protected JMenu createFileMenu() {
        JMenu fileMenu = new JMenu("File");
        fileMenu.setMnemonic(KeyEvent.VK_F);
        
        JMenuItem loadExample = new JMenuItem();
        loadExample.setAction(openExampleAction);          
        
        JMenuItem load = new JMenuItem();
        load.setAction(openFileAction);
        
        JMenuItem loadRecent = new JMenuItem();
        loadRecent.setAction(openMostRecentFileAction);
        
        JMenuItem edit = new JMenuItem();
        edit.setAction(editMostRecentFileAction);        
        
        JMenuItem save = new JMenuItem();
        save.setAction(saveFileAction);
        
        JMenuItem proofManagement = new JMenuItem();
        proofManagement.setAction(proofManagementAction);        
                                       
        JMenuItem exit = new JMenuItem("Exit");
        exit.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Q, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        exit.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                exitMain();
            }
        });
        
        JMenuItem userTacletsItem = new JMenuItem(loadUserDefinedTacletsAction);
      
        
        
        registerAtMenu(fileMenu, loadExample);        
        registerAtMenu(fileMenu, load);
        registerAtMenu(fileMenu, loadRecent);
        registerAtMenu(fileMenu, edit);
        registerAtMenu(fileMenu, save);        
        
        addSeparator(fileMenu);
        
        registerAtMenu(fileMenu, proofManagement);
        registerAtMenu(fileMenu, userTacletsItem);
        addSeparator(fileMenu);
        
        recentFiles = new RecentFileMenu(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                loadProblem(new File(recentFiles.getAbsolutePath((JMenuItem) e.getSource())));
            }
        }, MAX_RECENT_FILES, null);
        
        recentFiles.load(PathConfig.RECENT_FILES_STORAGE);
        
        registerAtMenu(fileMenu, recentFiles.getMenu());
        
        addSeparator(fileMenu);
        registerAtMenu(fileMenu, exit);
        return fileMenu;
    }
    
    protected JMenu createFontSizeMenuEntry() {
        final JMenu fontSize = new JMenu("Font Size");
        
        final JMenuItem smaller = new JMenuItem("Smaller");
        smaller.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Config.DEFAULT.smaller();
            }
        });
        
        int downMask = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
        switch (downMask) {
        case InputEvent.META_MASK : 
            downMask = InputEvent.META_DOWN_MASK; 
            break;        	
        default:
            // we default to Linux/Win
            downMask = InputEvent.CTRL_DOWN_MASK;
            break;
        }

        smaller.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, downMask));
        
        final JMenuItem larger = new JMenuItem("Larger");
        larger.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Config.DEFAULT.larger();
            }
        });
        larger.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_UP, downMask));
        
        Config.DEFAULT.addConfigChangeListener(new ConfigChangeListener() {
            public void configChanged(ConfigChangeEvent e) {
                smaller.setEnabled(!Config.DEFAULT.isMinimumSize());
                larger.setEnabled(!Config.DEFAULT.isMaximumSize());
            }            
        });
        
        fontSize.add(smaller);
        fontSize.add(larger);
        return fontSize;
    }
    
    protected JMenu createViewMenu() {
        JMenu view = new JMenu("View");
        view.setMnemonic(KeyEvent.VK_V);
        
        JMenuItem pretty = new JCheckBoxMenuItem("Use pretty syntax");
        pretty.setAccelerator(KeyStroke.getKeyStroke
                            (KeyEvent.VK_P, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));        
        pretty.setToolTipText("If ticked, infix notations are used.");
        pretty.setSelected(NotationInfo.PRETTY_SYNTAX);
	pretty.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    NotationInfo.PRETTY_SYNTAX=((JCheckBoxMenuItem)e.getSource()).
			isSelected();
		    makePrettyView();
		}});

	
	
	registerAtMenu(view, pretty);
	addSeparator(view);
		
	registerAtMenu(view, createFontSizeMenuEntry());
	
	final JMenuItem tacletOptionsView = new JMenuItem(TACLET_OPTIONS_MENU_STRING);

	tacletOptionsView.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    selectMaxTooltipLines();
		    tacletOptionsView.setText(TACLET_OPTIONS_MENU_STRING);
		    //+ "(" +
			// ProofSettings.DEFAULT_SETTINGS.getViewSettings().getMaxTooltipLines()
			// + ")");
		}});
	registerAtMenu(view, tacletOptionsView);
        
        
        return view;
    }
    
    protected JMenu createProofMenu() {
        JMenu proof = new JMenu("Proof");
        proof.setMnemonic(KeyEvent.VK_P);
        
	JMenuItem runStrategy = new JMenuItem(autoModeAction);
	registerAtMenu(proof, runStrategy);

	JMenuItem undo = new JMenuItem(new UndoLastStep(true));
	registerAtMenu(proof, undo);        
        
	JMenuItem close = new JMenuItem(new AbandonTask());
	registerAtMenu(proof, close);
	
	addSeparator(proof);        
	
        JMenuItem methodContractsItem = new JMenuItem("Show Used Contracts...");
        methodContractsItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
        	showUsedContracts();
            }});
        registerAtMenu(proof, methodContractsItem);	
        
        JMenuItem choiceItem = new JMenuItem("Show Active Taclet Options...");
        choiceItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showActivatedChoices();
            }});
        registerAtMenu(proof, choiceItem);
        
        
        JMenuItem showSettings = new JMenuItem("Show Active Settings...");
        showSettings.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showSettings();
            }
        });
        registerAtMenu(proof, showSettings);
        
        final JMenuItem statisticsInfo = new JMenuItem("Show Proof Statistics...");
        
        statisticsInfo.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
        	showStatistics();
            }
        });
        registerAtMenu(proof, statisticsInfo);
        
        final JMenuItem typeHierInfo = new JMenuItem("Show Known Types...");
        typeHierInfo.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showTypeHierarchy();
            }});
        registerAtMenu(proof, typeHierInfo);
        
        return proof;
    }

    protected JMenu createOptionsMenu() {
	JMenu options = new JMenu("Options");
	options.setMnemonic(KeyEvent.VK_O);
	
	// default taclet options
	JMenuItem choiceItem = new JMenuItem("Taclet Options...");
	choiceItem.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_T, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));

	choiceItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    selectChoices();
		}});
	registerAtMenu(options, choiceItem);	
    
        // SMT solvers
	createSMTMenu(options);

	smtSettingsListener = 
	    new SMTSettingsListener(ProofSettings.DEFAULT_SETTINGS.getSMTSettings());
               
        // specification languages
        JMenuItem speclangItem = setupSpeclangMenu();
        registerAtMenu(options, speclangItem);
        
        addSeparator(options);
        
        // minimize interaction
        final boolean stupidMode = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().tacletFilter();
        final JMenuItem stupidModeOption = new
            JCheckBoxMenuItem("Minimize Interaction", stupidMode);
        mediator.setStupidMode(stupidMode);
        
        stupidModeOption.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
                mediator().setStupidMode(b);
                ProofSettings.DEFAULT_SETTINGS.
                getGeneralSettings().setTacletFilter(b);
            }});
        registerAtMenu(options, stupidModeOption);
        
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
        
        
        // one step simplification
        final boolean oneStepSimplificationOn = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().oneStepSimplification();
        final JMenuItem oneStepSimplificationOption =
            new JCheckBoxMenuItem("One Step Simplification", oneStepSimplificationOn);
        oneStepSimplificationOption.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                boolean b = ((JCheckBoxMenuItem)e.getSource()).isSelected();           
                ProofSettings.DEFAULT_SETTINGS.
                getGeneralSettings().setOneStepSimplification(b);
                OneStepSimplifier.INSTANCE.refresh(mediator.getSelectedProof());
        }});
        registerAtMenu(options, oneStepSimplificationOption);
        mediator.addKeYSelectionListener(OneStepSimplifier.INSTANCE);
        
        return options;
    }
    
    
    
    
    /**
     * update the selection menu for Decisionprocedures.
     * Remove those, that are not installed anymore, add those, that got installed.
     */
    public void updateSMTSelectMenu() {
	
	//Collection<SMTRule> rules = ProofSettings.DEFAULT_SETTINGS.
	  //                             getSMTSettings().getInstalledRules();
	
	// TODO: Change this: only solver unions should be returned 
	// that are installed.
	Collection<SolverTypeCollection> solverUnions = ProofSettings.DEFAULT_SETTINGS.
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
	            	
		SolverTypeCollection active = ProofSettings.DEFAULT_SETTINGS.getSMTSettings().computeActiveSolverUnion();
		 
		SMTInvokeAction activeAction = findAction(actions, active);
		
		boolean found = activeAction != null;
		if(!found){
		    Object item = smtComponent.getTopItem();
		    if(item instanceof SMTInvokeAction){
			active = ((SMTInvokeAction)item).solverUnion;
			ProofSettings.DEFAULT_SETTINGS.getSMTSettings().setActiveSolverUnion(active);
		    }else{
			activeAction = null;
		    }

		}
		smtComponent.setSelectedItem(activeAction); 
	   }
    
    JCheckBoxMenuItem saveSMTFile;
    private JCheckBoxMenuItem waitForAllProvers;
    
    /**
     * creates a menu allowing to choose the external prover to be used
     * @return the menu with a list of all available provers that can be used
     */
    private void createSMTMenu(JMenu parent) {
	/** menu for configuration of SMT solvers */
        
        final SMTSettings smts = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();

	JMenuItem item = new JMenuItem("SMT Solvers...");
	item.addActionListener(new ActionListener() {
		   public void actionPerformed(ActionEvent e) {
		  
		       SettingsDialog.INSTANCE.showDialog(TemporarySettings.getInstance(
			       ProofSettings.DEFAULT_SETTINGS.getSMTSettings()));
		       
		       
		   }
		});
	registerAtMenu(parent, item);
    }    
    
    
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
    
    public JPanel getProofView(){
        return proofView;
    }
    
    public JMenu createHelpMenu() {
        JMenu help = new JMenu("About");
        help.setMnemonic(KeyEvent.VK_A);
        JMenuItem about = new JMenuItem("About KeY");
        about.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showAbout();
            }});
        help.add(about);	
        
        JMenuItem license = new JMenuItem("License");
        license.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showLicense();
            }});
        help.add(license);
        return help;
    }
    
    
    protected JMenu createDebugMenu() {
        JMenu debug = new JMenu("Debug");
        debug.setMnemonic(KeyEvent.VK_D);
        JMenuItem showSettings = new JMenuItem("Show settings");
        showSettings.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showSettings();
            }
        });
        debug.add(showSettings);
        return debug;
    }
    
    /** creates menubar entries and adds them to menu bar */
    private void createMenuBarEntries() {
        JMenuBar menuBar = getJMenuBar();
        menuBar.add(createFileMenu());
        menuBar.add(createViewMenu());
        menuBar.add(createProofMenu());
        menuBar.add(createOptionsMenu());
        menuBar.add(Box.createHorizontalGlue());
        menuBar.add(createHelpMenu());
        if (Debug.ENABLE_DEBUG)
            menuBar.add(createDebugMenu());
    }
    
    /**
     * returns the toolbar
     */
    public JToolBar getToolBar() {
        return toolBar;
    }
    
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
    public void printSequentView(Sequent sequent) {
        SequentPrintFilter filter = new IdentitySequentPrintFilter ( sequent );
        final LogicPrinter printer = new LogicPrinter
        (new ProgramPrinter(null), 
                mediator().getNotationInfo(),
                mediator.getServices());
                
        sequentView.setPrinter(printer, filter, null);
        sequentView.printSequent();
        
        updateGoalView("Current Goal", sequentView);
    }
    
    
    public static KeYFileChooser getFileChooser(String title) {
        if (fileChooser == null) {
            String initDir = fileNameOnStartUp == null 
                             ? System.getProperty("user.dir")
                             : fileNameOnStartUp;
            fileChooser = new KeYFileChooser(initDir);
        }
        fileChooser.setDialogTitle(title);
        fileChooser.prepare();
        return fileChooser;
    }
    
    /** saves a proof */
    protected void saveProof() {
        final KeYFileChooser jFC = getFileChooser("Choose filename to save proof");
        final String defaultName 
        	= MiscTools.toValidFileName(mediator.getSelectedProof()
        		                            .name()
        		                            .toString()).toString();
        boolean saved = jFC.showSaveDialog(this, defaultName + ".proof");
        if (saved) {
            saveProof(jFC.getSelectedFile());
        }
    }
    
    protected void saveProof(String proofFile) {
        saveProof(new File(proofFile));
    }
    
    protected void saveProof(File proofFile) {
        String filename = proofFile.getAbsolutePath();    
        ProofSaver saver = new ProofSaver(mediator().getSelectedProof(), filename,this.getInternalVersion());
        String errorMsg ;
        try{
         errorMsg= saver.save();
        }catch(IOException e){
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
        pl.addTaskListener(getProverTaskListener());
        pl.run();
    }
    
    protected void closeTask() {
	final Proof proof = mediator.getProof();
	if (proof != null) {
	    final TaskTreeNode rootTask = proof.getBasicTask().getRootTask();
	    closeTask(rootTask); 
	}
    }

    protected void closeTask(TaskTreeNode rootTask) {
       if(proofList.removeTask(rootTask)){
            for(Proof proof:rootTask.allProofs()){
                //In a previous revision the following statement was performed only
                //on one proof object, namely on: mediator.getProof()
                proof.getServices().getSpecificationRepository().removeProof(proof);
                proof.mgt().removeProofListener();
            }
            ((ProofTreeView)proofView.getComponent(0)).removeProofs(rootTask.allProofs());
       }
    }

    
    public void closeTaskWithoutInteraction() {
        final Proof proof = mediator.getProof();
        if (proof != null) {
            final TaskTreeNode rootTask = 
                proof.getBasicTask().getRootTask();     
            proofList.removeTaskWithoutInteraction(rootTask);   
            proof.getServices().getSpecificationRepository().removeProof(proof);
            proof.mgt().removeProofListener();
            ((ProofTreeView)proofView.getComponent(0)).removeProofs(rootTask.allProofs());
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
        if (SwingUtilities.isEventDispatchThread())
            guiUpdater.run();
        else
            KeYMediator.invokeAndWait(guiUpdater);
    }
    
    protected Proof setUpNewProof(Proof proof) {
        mediator().setProof(proof);
        return proof;
    }
    
    private java.util.Hashtable<Component, Component> doNotEnable;
    
    private void setToolBarDisabled() {
        doNotEnable = new java.util.Hashtable<Component, Component>(10);
        Component[] cs = toolBar.getComponents();
        int i = cs.length;
        while (i-- != 0) {
            if (!cs[i].isEnabled())
                doNotEnable.put(cs[i], cs[i]);
            cs[i].setEnabled(false);
        }
    }
    
    private void setToolBarEnabled() {
        Component[] cs = toolBar.getComponents();
        int i = cs.length;
        while (i-- != 0) {
            if (!doNotEnable.containsKey(cs[i]))
                cs[i].setEnabled(true);
        }
    }
    
    private final class SMTSettingsListener implements SettingsListener {	
	private SMTSettings settings;

	public SMTSettingsListener(SMTSettings dps) {
	    this.settings = dps;
	    register();
	}

	private void register() {
	    if (settings != null) {
		settings.addSettingsListener(this);
	    }
	}

	private void unregister() {
	    if (settings != null) {
		settings.removeSettingsListener(this);
	    }
	}
	
	public void update() {	   
	    
	    if (settings != null) {
		updateSMTSelectMenu();

	    } else {
		assert false;
	    }
	}

	public void settingsChanged(GUIEvent e) {
	    if (e.getSource() instanceof SMTSettings) {
		if (e.getSource() != settings) {
		    unregister();
		    settings = (SMTSettings) e.getSource();		    
		    register();
		}
		update();
	    }
	}
    }
    
    
    
    /**
     * Opens a file dialog allowing to select the file to be loaded
     */
    private final class OpenFile extends AbstractAction {
        public OpenFile() {
            putValue(NAME, "Load...");
            putValue(SMALL_ICON, IconFactory.openKeYFile(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Browse and load problem or proof files.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_O, 
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        }
        
        public void actionPerformed(ActionEvent e) {
            KeYFileChooser keYFileChooser = getFileChooser("Select file " + "to load proof "
                    + "or problem");
            boolean loaded = keYFileChooser.showOpenDialog(Main.this);
            if (loaded) {
                File file = keYFileChooser.getSelectedFile();
                loadProblem(file);
            }
            
        }
    }
    

    /**
     * Opens a file dialog allowing to select the example to be loaded
     */
    private final class OpenExample extends AbstractAction {
        public OpenExample() {
            putValue(NAME, "Load Example...");
            putValue(SHORT_DESCRIPTION, "Browse and load included examples.");
        }
        
        public void actionPerformed(ActionEvent e) {
            File file = ExampleChooser.showInstance(examplesDir);
            if(file != null) {
        	loadProblem(file);
            }
        }
    }    
    

    /**
     * Loads the last opened file
     */
    private final class OpenMostRecentFile extends AbstractAction {
        
        public OpenMostRecentFile() {
            putValue(NAME, "Reload ");
            putValue(SMALL_ICON, IconFactory.openMostRecent(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Reload last opened file.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_R,  
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        }
        
        public void actionPerformed(ActionEvent e) {
            if (recentFiles != null && recentFiles.getMostRecent() != null) {
                final String recentFile = recentFiles.getMostRecent().getAbsolutePath();
                if (recentFile != null) {
                    loadProblem(new File(recentFile));
                }
            }
        }
    }    
    

    
    /**
     * Opens the last opened file in an editor (well, it tries)
     */
    private final class EditMostRecentFile extends AbstractAction {        
        public EditMostRecentFile() {
            putValue(NAME, "Edit");            
            putValue(SMALL_ICON, IconFactory.editFile(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Edit last opened file.");     
            if(!Desktop.isDesktopSupported()
               || (!Desktop.getDesktop().isSupported(Desktop.Action.EDIT) 
                   && !Desktop.getDesktop().isSupported(Desktop.Action.OPEN))) {
        	setEnabled(false);
            }
        }
        
        public void actionPerformed(ActionEvent e) {
            if(recentFiles != null && recentFiles.getMostRecent() != null) {
        	Desktop d = Desktop.getDesktop();
                final String recentFile = recentFiles.getMostRecent()
                                                     .getAbsolutePath();
                if(recentFile != null) {
                    File f = new File(recentFile);
                    try {
                	if(d.isSupported(Desktop.Action.EDIT) && f.isFile()) {
                	    d.edit(f);
                	} else {
                	    d.open(f);
                	}
                    } catch(Exception exc) {
                	setEnabled(false);
                    }
                }
            }
        }
    }            
    
    
    /**
     * Saves the current selected proof.
     */
    private final class SaveFile extends AbstractAction {
        
        public SaveFile() {
            putValue(NAME, "Save ...");
            putValue(SMALL_ICON, IconFactory.saveFile(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Save current proof.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_S,  
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
            
            mediator.enableWhenProof(this);
        }
        
        public void actionPerformed(ActionEvent e) {
            if (mediator().ensureProofLoaded()) {
                saveProof();
            }
        }
    }
    
    
    
    /**
     * Shows the proof management dialog
     */
    private final class ProofManagementAction extends AbstractAction {
        
        public ProofManagementAction() {
            putValue(NAME, "Proof Management...");
            putValue(SHORT_DESCRIPTION, "Proof Management.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_M, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
            
            setEnabled(enabled());
            
            mediator.addKeYSelectionListener(new KeYSelectionListener() {
                /** focused node has changed */
                public void selectedNodeChanged(KeYSelectionEvent e) {
                }
                
                /**
                 * the selected proof has changed. Enable or disable action depending whether a proof is
                 * available or not
                 */ 
                public void selectedProofChanged(KeYSelectionEvent e) {
                    setEnabled(enabled());
                }
            });
        }
        
        private boolean enabled() {
            return mediator.getProof() != null 
                   && mediator.getProof().getJavaModel() != null
                   && !mediator.getProof().getJavaModel().isEmpty();
        }
        
        
        public void actionPerformed(ActionEvent e) {
            showProofManagement();
        }
    }
    
    private final class LoadUserDefinedTacletsAction extends AbstractAction{


        private static final long serialVersionUID = 1L;

        public LoadUserDefinedTacletsAction() {
                putValue(NAME, "Load User-Defined Taclets...");
                putValue(SHORT_DESCRIPTION, "Loads additional taclets and creates the corresponding proofs.");
                mediator.enableWhenProof(this);
        }
        
        private void loadTaclets(){
                FileChooser chooser = new FileChooser();
  
                boolean loaded = chooser.showAsDialog();

                if (!loaded){
                        return;
                }
                final Proof proof = mediator().getSelectedProof();
                final File fileForLemmata = chooser.getFileForLemmata();
                final File fileForDefinitions = chooser.getFileForDefinitions();

                
                List<File> filesForAxioms = chooser.getFilesForAxioms();



                LoaderListener listener =   new LoaderListener() {
                        @Override 
                        public void stopped(Throwable exception) {
                                handleException(exception);
                        }           
                        @Override
                        public void stopped(ProofAggregate p, ImmutableSet<Taclet> taclets) {
                                mediator().startInterface(true);
                                if(p != null){
                                        
                                        Main.this.addProblem(p);
                                        // add only the taclets to the goals if 
                                        // the proof obligations were added successfully.
                                        ImmutableSet<Taclet> base =
                                                proof.env().getInitConfig().getTaclets();
                                        base = base.union(taclets);
                                        proof.env().getInitConfig().setTaclets(base);
                                        for(Taclet taclet : taclets){
                                                for(Goal goal : proof.openGoals()){
                                                        goal.addTaclet(taclet, 
                                                           SVInstantiations.EMPTY_SVINSTANTIATIONS,false);
                                                }
                                        }
                                }
                        }

                        @Override
                        public void started() {
                                mediator().stopInterface(true);         
                        }
                };


                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(progressMonitor, 
                                fileForLemmata,proof.env() ,listener,piListener,
                                new LemmaSelectionDialog(),filesForAxioms,
                                fileForDefinitions);
                loader.start();
                 
        }
        
        private void handleException(Throwable exception){
                String desc = exception.getMessage();
                SimpleExceptionDialog.INSTANCE.showDialog("Error while loading taclets:",desc, exception); 
        }
        
        @Override
        public void actionPerformed(ActionEvent e) {
                try{
                      loadTaclets();        
                }catch(Throwable exception){
                      handleException(exception);  
                }
                
        }
               
            
    }
    
    
    /**
     * The progress monitor that displays a progress bar in a corner of the main window.
     */
    class MainProgressMonitor implements ProgressMonitor {
        public void setProgress(int progress) {
            if (SwingUtilities.isEventDispatchThread())
                statusLine.setProgress(progress);
            else {
                final int v = progress;
                Runnable lineUpdater = new Runnable() {
                    public void run() {
                        statusLine.setProgress(v);
                    }
                };
                SwingUtilities.invokeLater(lineUpdater);
            }
        }
        
        public void setMaximum(int maximum) {
            statusLine.setProgressBarMaximum(maximum);
        }
    }
    
    class MainListener extends WindowAdapter {
        public void windowClosing(WindowEvent e) {
            exitMain();
        }
    }    
    
    class MainGUIListener implements GUIListener {
        /** invoked if a frame that wants modal access is opened */
        
        private void enableMenuBar(JMenuBar m, boolean b) {
            for (int i = 0; i < m.getMenuCount(); i++) {
                if (m.getMenu(i) != null) { // otherwise it is a spacer
                    m.getMenu(i).setEnabled(b);
                }
            }
        }
        
        public void modalDialogOpened(GUIEvent e) {
            
            if (e.getSource() instanceof ApplyTacletDialog) {
                // disable all elements except the sequent window (drag'n'drop !) ...
                enableMenuBar(Main.this.getJMenuBar(), false);
                Main.this.goalView.setEnabled(false);
                Main.this.proofView.setEnabled(false);
                Main.this.openGoalsView.setEnabled(false);
                Main.this.strategySelectionView.setEnabled(false);
                Main.this.ruleView.setEnabled(false);
                setToolBarDisabled();
            } else {
                // disable the whole main window ...
                Main.this.setEnabled(false);
            }
        }
        
        /** invoked if a frame that wants modal access is closed */
        public void modalDialogClosed(GUIEvent e) {
            if (e.getSource() instanceof ApplyTacletDialog) {
                // enable all previously diabled elements ...
                enableMenuBar(Main.this.getJMenuBar(), true);
                Main.this.goalView.setEnabled(true);
                Main.this.proofView.setEnabled(true);
                Main.this.openGoalsView.setEnabled(true);
                Main.this.strategySelectionView.setEnabled(true);
                Main.this.ruleView.setEnabled(true);
                setToolBarEnabled();
            } else {
                // enable the whole main window ...
                Main.this.setEnabled(true);
            }
        }
        
        public void shutDown(GUIEvent e) {
            Main.this.notify(new ExitKeYEvent());
            Main.this.setVisible(false);
        }
        
    }
    
    /**
     * set to true if the view of the current goal should not be updated
     */
    private boolean disableCurrentGoalView = false;

   

    private synchronized void setProofNodeDisplay() {
        if (!disableCurrentGoalView) {
            Goal goal;
            if(mediator()!=null && mediator().getSelectedProof()!=null){
                goal = mediator().getSelectedGoal();
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
                    new NonGoalInfoView(mediator().getSelectedNode(), 
                            mediator());
                updateGoalView("Inner Node", innerNodeView);
            }
        }
    }
    
    class MainProofListener implements AutoModeListener, KeYSelectionListener,
    	SettingsListener {	
        
        Proof proof = null;
        
        
        /** focused node has changed */
        public synchronized void selectedNodeChanged(KeYSelectionEvent e) {
            if (mediator().autoMode()) return;
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
            smtSettingsListener.settingsChanged(new GUIEvent((proof != null ? 
        	    proof.getSettings() : ProofSettings.DEFAULT_SETTINGS).getSMTSettings()));
            makePrettyView();
        }
        
        /**
         * invoked if automatic execution has started
         */
        public synchronized void autoModeStarted(ProofEvent e) {
            Debug.log4jWarn("Automode started", Main.class.getName());
            disableCurrentGoalView = true;
            mediator().removeKeYSelectionListener(proofListener);
            freezeExceptAutoModeButton();
        }
        
        /**
         * invoked if automatic execution has stopped
         */
        public synchronized void autoModeStopped(ProofEvent e) {
            Debug.log4jWarn("Automode stopped", Main.class.getName());
            Debug.log4jDebug("From " + Debug.stackTrace(), Main.class.getName());
            unfreezeExceptAutoModeButton();
            disableCurrentGoalView = false;
            setProofNodeDisplay();
            mediator().addKeYSelectionListener(proofListener);
        }
        
        /** invoked when the strategy of a proof has been changed */
        public synchronized void settingsChanged ( GUIEvent e ) {
            if ( proof.getSettings().getStrategySettings() == (StrategySettings) e.getSource() ) {
                // updateAutoModeConfigButton();
            }         
        }
        
    }
        

    /** displays some status information */
    private void displayResults ( long time, int appliedRules, int closedGoals ) {
        String message;       
        String timeString = "" + (time/1000)+"."+((time%1000)/100);        
        
        int closed = mediator().getNrGoalsClosedByAutoMode();
        
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
            
            String fileName = fileNameOnStartUp;
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
     * called when the batch mode has been finished 
     * @param result the Object encapsulating informtation about the result, e.g.
     * String "Error" if an error has occurred. 
     * @param proof the Proof to which <tt>appliedRules</tt> rules have been 
     * applied requiring <tt>time</tt> ms
     * @param time the long giving the needed time in ms 
     * @param appliedRules the int giving the number of applied rules
     */
    private void finishedBatchMode (Object result, 
            Proof proof, long time, int appliedRules) {

        if ( Main.statisticsFile != null )
            printStatistics ( Main.statisticsFile, result, time, appliedRules );

        if ("Error".equals ( result ) ) {
            // Error in batchMode. Terminate with status -1.
            System.exit ( -1 );
        }

        // Save the proof before exit.

        String baseName = Main.fileNameOnStartUp;
        int idx = baseName.indexOf(".key");        
        if (idx == -1) {
            idx = baseName.indexOf(".proof");
        }        
        baseName = baseName.substring(0, idx==-1 ? baseName.length() : idx);

        File f; 
        int counter = 0;
        do {           

            f = new File(baseName + ".auto."+ counter +".proof");
            counter++;
        } while (f.exists());

        Main.getInstance ().saveProof ( f.getAbsolutePath() );
        if (proof.openGoals ().size () == 0) {
            // Says that all Proofs have succeeded
            if (proof.getBasicTask().getStatus().getProofClosedButLemmasLeft()) {
                // Says that the proof is closed by depends on (unproved) lemmas                
                System.exit ( 0 ); //XXX, was: 2 
            }
            System.exit ( 0 ); 
        } else {
            // Says that there is at least one open Proof
            System.exit ( 1 );
        }
    }

    class MainTaskListenerBatchMode implements ProverTaskListener { // XXX
        public void taskStarted(String message, int size) {
            System.out.print(message+" ... ");
        }
        
        public void taskProgress(int position) {
        }
        
        public void taskFinished(TaskFinishedInfo info) {
            System.out.println("[ DONE ]");
            if (info.getSource() instanceof ApplyStrategy) {
                finishedBatchMode ( info.getResult(), 
                        info.getProof(), info.getTime(), 
                        info.getAppliedRules());
                Debug.fail ( "Control flow should not reach this point." );
            } else if (info.getSource() instanceof ProblemLoader) {
                if (!"".equals(info.getResult())) {
                        System.exit(-1);
                } 
                if(info.getProof().openGoals().size()==0) {
                    System.out.println("proof.openGoals.size=" + 
                            info.getProof().openGoals().size());              
                    System.exit(0);
                }
                mediator.startAutoMode();
            }
        }
    }
    
    class MainTaskListener implements ProverTaskListener { // XXX
        public void taskStarted(String message, int size) {
            final MainStatusLine sl = getStatusLine();
            sl.reset();
            if (size > 0) {
                sl.setProgressPanelVisible(true);
                getProgressMonitor().setMaximum(size);
            }
            sl.setStatusText(message);
        }
        
        public void taskProgress(int position) {
            getProgressMonitor().setProgress(position);
        }
        
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
                            new ExceptionDialog(Main.this,     
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
    }
    
    public static void evaluateOptions(String[] opt) {
	int index = 0;
	ProofSettings.DEFAULT_SETTINGS.setProfile(new JavaProfile());
	while (opt.length > index) {	    
	    if ((new File(opt[index])).exists()) {
		fileNameOnStartUp=opt[index];
	    } else {
		opt[index] = opt[index].toUpperCase();		
		if (opt[index].equals("NO_DEBUG")) {
		    de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;
		} else if (opt[index].equals("DEBUG")) {
		    de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = true;
		} else if (opt[index].equals("NO_ASSERTION")) {
		    de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = false;
		} else if (opt[index].equals("ASSERTION")) {
		    de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = true;
		} else if (opt[index].equals("NO_JMLSPECS")) {
		    GeneralSettings.disableSpecs = true;
		} else if (opt[index].equals("JUSTIFYRULES")){
		  LinkedList<String> options = new LinkedList<String>();
		  for(int i = index+1; i < opt.length; i++){
		      options.add(opt[i]);
		  }
		  evaluateLemmataOptions(options);
		  // is last option 
		  break; 
		}else if (opt[index].equals("AUTO")) {
		    batchMode = true;
                    visible = false;
		} else if (opt[index].equals("TIMEOUT")) {
                    long timeout = -1;
                    try {
                        timeout = Long.parseLong(opt[index + 1]);
                    } catch (NumberFormatException nfe) {
                        System.out.println("Illegal timeout (must be a number >=-1).");
                        System.exit(-1);
                    }
                    if (timeout < -1) {
                        System.out.println("Illegal timeout (must be a number >=-1).");
                        System.exit(-1);                        
                    }
                    index++;                   
                    ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
		} else if (opt[index].equals("PRINT_STATISTICS")) {                     
		    if ( !( opt.length > index + 1 ) ) printUsageAndExit ();
		    statisticsFile = opt[++index];
		} else if(opt[index].equals("EXAMPLES")) {
		    if ( !( opt.length > index + 1 ) ) printUsageAndExit ();
		    examplesDir = opt[++index];
		} else {
		    printUsageAndExit ();
		}		
	    }
	    index++;
	}	
	if (Debug.ENABLE_DEBUG) {
	    System.out.println("Running in debug mode ...");
	} else {
	    System.out.println("Running in normal mode ...");
	}
	if (Debug.ENABLE_ASSERTION) {
	    System.out.println("Using assertions ...");	   
	} else {
	    System.out.println("Not using assertions ...");	   
	}
    }
    
    private static void evaluateLemmataOptions(LinkedList<String>  options){
	LemmataAutoModeOptions opt;
	try{
	    
	    opt = new LemmataAutoModeOptions(options,getInstance(false).getInternalVersion(), 
		    PathConfig.KEY_CONFIG_DIR
		    );
	}catch(Throwable e){
	    System.out.println("An error occured while reading the parameters:");
	    System.out.println(e.getMessage());
	    e.printStackTrace();
	    System.exit(1);
	    return;
	}
	KeYMediator mediator = getInstance(false).mediator();

	try{
	LemmataHandler handler = new LemmataHandler(opt,
			mediator.getProfile());
	handler.start();
	}
	catch(ProofInputException exception){
	    System.out.println("Could not create dummy file: " + exception);
	}
	catch(IOException exception){
	    System.out.println("Could not create dummy file: " + exception);
	}

   }

    private static void printUsageAndExit() {
        System.out.println("File not found or unrecognized option.\n");
        System.out.println("Possible parameters are (* = default): ");
        System.out.println("  no_debug        : disables debug mode (*)");
        System.out.println("  debug           : enables debug mode");
        System.out.println("  no_assertion    : disables assertions");
        System.out.println("  assertion       : enables assertions (*)");
        System.out.println("  no_jmlspecs     : disables parsing JML specifications");
        System.out.println("  auto	      : start prove procedure after initialisation");
        System.out.println("  print_statistics <filename>" );
        System.out.println("                  : in auto mode, output nr. of rule applications and time spent");
        System.out.println("  timeout <time in ms>");
        System.out.println("                  : set maximal time for rule " +
                            "application in ms (-1 disables timeout)");
        System.out.println("  <filename>      : loads a .key file");
        System.exit(-1);
    }
    
    
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
    
    
    /**
     * This action undoes the last rule application on the currently selected
     * branch (if not closed).
     *
     * The action is enabled if a goal is selected. 
     */
    private final class UndoLastStep extends AbstractAction {

	private boolean longName = false;
	
	/**
	 * creates an undo action
	 * @param longName a boolean true iff the long name should be shown (e.g. in MenuItems)
	 */
        public UndoLastStep(boolean longName) {            
            this.longName = longName;
            init();
            setBackMode();
        }

        /** 
         * Registers the action at some listeners to update its status
         * in a correct fashion. This method has to be invoked after the
         * Main class has been initialised with the KeYMediator.
         */
        public void init() {
            final KeYSelectionListener selListener = new KeYSelectionListener() {

                public void selectedNodeChanged(KeYSelectionEvent e) {
                    final Proof proof = mediator.getSelectedProof();
                    if (proof == null) {
                        // no proof loaded
                        setEnabled(false);
                    } else {
                        final Goal selGoal = mediator.getSelectedGoal();
                        final Node selNode = mediator.getSelectedNode();

                        if (selGoal == null && selNode == null) {
                            setBackMode();
                            setEnabled(false);
                        } else if (selGoal != null) {
                            /* we undo the last rule application, if
                             * the goal refers not to the proof's root */
                            setBackMode();
                            setEnabled(selNode != proof.root());
                        } else {/* pruning instead of goal back */
                            // pruning a tree only if the selected node has children
                            // and sub tree is not closed
                            pruneMode();
                            setEnabled(!(selNode.leaf() || selNode.isClosed()));
                        }
                    }
                }
                
                public void selectedProofChanged(KeYSelectionEvent e) {
                    selectedNodeChanged(e);
                }                
            };
            
            mediator.addKeYSelectionListener(selListener);
            
            mediator.addAutoModeListener(new AutoModeListener() {
                public void autoModeStarted(ProofEvent e) {
                    mediator.removeKeYSelectionListener(selListener);
                    setEnabled(false);
                }

                public void autoModeStopped(ProofEvent e) {
                    mediator.addKeYSelectionListener(selListener);
                    selListener.selectedNodeChanged(null);
                }                
            });
            selListener.selectedNodeChanged(new KeYSelectionEvent(mediator.getSelectionModel()));
        }
        
        private void setBackMode() {
            String appliedRule = "";

            if (longName && mediator != null) {
        	final Node nd = mediator.getSelectedNode();
            
        	if (nd != null && nd.parent() != null 
        		&&  nd.parent().getAppliedRuleApp() != null) {
        	    appliedRule = 
        		" (" + nd.parent().getAppliedRuleApp().rule().displayName() + ")";
        	}
            }
            putValue(NAME, "Goal Back" + appliedRule );
            
            putValue(SMALL_ICON, 
                    IconFactory.goalBackLogo(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Undo the last rule application.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_Z,
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        }

        private void pruneMode() {
            putValue(NAME, "Prune Proof");
            putValue(SMALL_ICON, IconFactory.goalBackLogo(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, 
                    "Prune the tree below the selected node.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_Z,
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));

        }
        
        public void actionPerformed(ActionEvent e) {            
            final Goal selGoal = mediator.getSelectedGoal();
            if (selGoal != null) {
                mediator.setBack(selGoal);                
            } else {
                mediator.setBack(mediator.getSelectedNode());
            }
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
	        
	            SMTSettings settings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
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
    
    
    private final class AbandonTask extends AbstractAction  {
	public AbandonTask() {
	    putValue(NAME, "Abandon");
	    putValue(ACCELERATOR_KEY, KeyStroke.
		    getKeyStroke(KeyEvent.VK_W, 
			    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
	    
            mediator.enableWhenProof(this);
	}
			      
	public void actionPerformed(ActionEvent e) {
	    closeTask();
	}

    }    
    
  
    private final class AutoModeAction extends AbstractAction {
        final Icon startLogo = 
            IconFactory.autoModeStartLogo ( TOOLBAR_ICON_SIZE );
        final Icon stopLogo = 
            IconFactory.autoModeStopLogo ( TOOLBAR_ICON_SIZE );
        
        private Proof associatedProof;
        
        private final ProofTreeListener ptl = new ProofTreeAdapter() {
            
            public void proofStructureChanged(ProofTreeEvent e) {
                if (e.getSource() == associatedProof) {
                    enable();
                }
            }
            
            public void proofClosed(ProofTreeEvent e) {
                if (e.getSource() == associatedProof) {
                    enable();
                }
            }
	    
	    public void proofGoalsAdded(ProofTreeEvent e) {
	        Proof p = e.getSource();
		ImmutableList<Goal> newGoals = e.getGoals();
		// Check for a closed goal ...
		if ((newGoals.size() == 0)&&(!p.closed())){
		    // No new goals have been generated ...
                    setStatusLine("1 goal closed, "+
		        p.openGoals().size()+" remaining");
		}
	    }
        };
        
        public void enable() {
            setEnabled(associatedProof != null && !associatedProof.closed());            
        }
        
        private String getStartCommand() {
            if (associatedProof != null && !associatedProof.root().leaf()) {
        	return "Continue";
            } else {
        	return "Start";
            }
        }
        
        public AutoModeAction() {            
            associatedProof = mediator.getProof();        
            putValue("hideActionText", Boolean.TRUE);
            putValue(Action.NAME, getStartCommand());
            putValue(Action.SHORT_DESCRIPTION, AUTO_MODE_TEXT);
            putValue(Action.SMALL_ICON, startLogo);
            putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_A,
        	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
            
            enable();
            
            if (associatedProof != null && !associatedProof.containsProofTreeListener(ptl)) {
                associatedProof.addProofTreeListener(ptl);                
            }
            
            
            mediator.addKeYSelectionListener(new KeYSelectionListener() {
                /** focused node has changed */
                public void selectedNodeChanged(KeYSelectionEvent e) {}
                
                /**
                 * the selected proof has changed. Enable or disable action depending whether a proof is
                 * available or not
                 */ 
                public void selectedProofChanged(KeYSelectionEvent e) {
                    if (associatedProof != null) {
                        associatedProof.removeProofTreeListener(ptl);
                    }
                    
                    associatedProof = e.getSource().getSelectedProof();                     
                    enable();                       
                    
                    if (associatedProof != null) {
                        associatedProof.addProofTreeListener(ptl);
                    }
                }
            });
            
            mediator.addAutoModeListener(new AutoModeListener() {
                
                /** 
                 * invoked if automatic execution has started
                 */
                public void autoModeStarted(ProofEvent e) {                        
                    if (associatedProof != null) {
                        associatedProof.removeProofTreeListener(ptl);                        
                    }
                    putValue(Action.NAME, "Stop");
                    putValue(Action.SMALL_ICON, stopLogo);
                }
                
                /**
                 * invoked if automatic execution has stopped
                 */
                public void autoModeStopped(ProofEvent e) {
                    if (associatedProof != null && 
                            associatedProof == e.getSource() && 
                            !associatedProof.containsProofTreeListener(ptl) ) {
                        associatedProof.addProofTreeListener(ptl);
                    }
                    putValue(Action.NAME, getStartCommand());
                    putValue(Action.SMALL_ICON, startLogo);
                }
                
            });
            
        }
        
        public void actionPerformed(ActionEvent e) {
            // Unfortunately, when clicking the button twice
            // (very fast), the glasspane won't be quick
            // enough to catch the second event. Therefore
            // we make a second check (which is a %%%HACK)
            if (!frozen)
                mediator().startAutoMode();
            else {
        	mediator().interrupted(e);
                mediator().stopAutoMode();
            }
        }
        
    }
    
    public void loadCommandLineFile() {
        if (fileNameOnStartUp != null) {
            loadProblem(new File(fileNameOnStartUp));
        } else if(examplesDir != null) {
            openExampleAction.actionPerformed(null);
        }
    }
    
    public static void main(String[] args) {
        System.out.println("\nKeY Version " + VERSION);
	System.out.println(COPYRIGHT+"\nKeY is protected by the " +
	      	           "GNU General Public License\n");
        
        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar","true"); 
 	
        Main.evaluateOptions(args);        
 	Main key = getInstance(visible);   
 	key.loadCommandLineFile();
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
    
    
    public static void setVisibleMode(boolean visible) {
	Main.visible = visible;
    }    
}
