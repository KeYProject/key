// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.Dimension;
import java.awt.event.*;
import java.io.*;
import java.net.URL;
import java.util.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.*;
import javax.swing.text.JTextComponent;

import org.apache.log4j.Logger;

import de.uka.ilkd.hoare.init.HoareProfile;
import de.uka.ilkd.hoare.pp.HoareLogicPrettyPrinter;
import de.uka.ilkd.key.gui.assistant.*;
import de.uka.ilkd.key.gui.configuration.*;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.*;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.decproc.DecProcRunner;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAuflia;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.unittest.UnitTestBuilder;
import de.uka.ilkd.key.util.*;
import de.uka.ilkd.key.util.ProgressMonitor;

public class Main extends JFrame {

    public static final String INTERNAL_VERSION = 
	KeYResourceManager.getManager().getSHA1();

    private static final String VERSION = 
	KeYResourceManager.getManager().getVersion() + 
	"-beta (internal: "+INTERNAL_VERSION+")";

    private static final String COPYRIGHT="(C) Copyright 2001-2007 "
        +"Universit\u00e4t Karlsruhe, Universit\u00e4t Koblenz-Landau, "
        +"and Chalmers University of Technology";
    
    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;
    
    /**
     * In which file to store the recent files.
     */
    private static final String RECENT_FILES_STORAGE = System.getProperty("user.home")
    + File.separator + ".key" + File.separator + "recentFiles.props";
    
    /** Name of the config file controlling logging with log4j */
    private static final String LOGGER_CONFIGURATION = System.getProperty("user.home")
    + File.separator + ".key" + File.separator + "logger.props";
    
    static {
        // @xxx preliminary: better store along with other settings.
        PresentationFeatures.ENABLED = true;
    }
    
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
    
    /** the KeY test generator GUI*/
    private UnitTestGeneratorGui unitKeY;
    
    /** the user constraint view */
    private UserConstraintView userConstraintView = null;
    
    /** the rule view */
    private RuleView ruleView = null;
    
    /** the strategy selection view */
    private StrategySelectionView strategySelectionView = null;
    
    /** the current user constraint */
    private ConstraintTableModel userConstraint = null;
    
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
    
    /** listener to changes of the user constraint */
    private MainConstraintTableListener constraintListener;
     
    private static KeYFileChooser fileChooser = null;
    
    private static final String PARA = 

       "<p style=\"font-family: lucida;font-size: 12pt;font-weight: bold\">";
       
    /** button for starting and stopping automatic mode */
    public static AutoModeAction autoModeAction;
    
    /** action for opening a KeY file */
    public static OpenFile openFileAction;
    
    /** action for saving a proof (attempt) */
    public static SaveFile saveFileAction;
    

    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";

    /** if true then automaticaly start startAutoMode after the key-file is loaded*/

    public static boolean batchMode = false;
    
    /** A push-button test generation view of KeY*/
    public static boolean testStandalone = false;
    
    /** Determines if the KeY prover is started in visible mode*/
    public static boolean visible = true;

    public static String statisticsFile = null;

    /** if true then the prover starts in 
     * a unit test generation optimized mode.
     * ATTENTION: to be deleted (Puse profiles to customize 
     * JML translation, TODO)
     * */ 

    public static boolean testMode = false;

    /** if false then JML specifications are not parsed (useful for .key input) */
    public static boolean jmlSpecs = true;
    
    public JButton reuseButton = new JButton("Reuse",IconFactory.reuseLogo());
    
    private JButton decisionProcedureButton;
    
    private JButton testButton;
    
    private JPopupMenu reusePopup = new JPopupMenu();
    
    protected static String fileNameOnStartUp = null;
    
    /** are we in stand-alone mode? (or with TCC?) */
    public static boolean standalone = System.getProperty("key.together") == null;
    
    /** for locking of threads waiting for the prover to exit */
    public Object monitor = new Object();
    
    private static final String TACLET_OPTIONS_MENU_STRING = "ToolTip options ";
    
    private Action createUnitTestAction = null;
    
    
    protected static Main instance = null;
    
    /** menu for configuration of decision procedure */
    JMenu decisionProcedureOption = new JMenu("Decision Procedures");
    
    JRadioButtonMenuItem simplifyButton = new JRadioButtonMenuItem("Simplify", true);
    
    JRadioButtonMenuItem icsButton = new JRadioButtonMenuItem("ICS", false);
    
    JRadioButtonMenuItem cvcLiteButton = new JRadioButtonMenuItem("CVCLite", false);

    JRadioButtonMenuItem cvc3Button = new JRadioButtonMenuItem("CVC3", false);
    
    JRadioButtonMenuItem svcButton = new JRadioButtonMenuItem("SVC", false);

    JRadioButtonMenuItem yicesButton = new JRadioButtonMenuItem("Yices", false);
    
    JRadioButtonMenuItem smtButton = new JRadioButtonMenuItem("SMT Translation", false);
           
    JMenuItem smtUseQuantifiersOption;
    
    JMenuItem smtBenchmarkArchivingOption;
    
    JMenuItem smtZipProblemDirOption;
    
    
    /** size of the tool bar icons */
    private int toolbarIconSize = 15;
    
    private ProverTaskListener taskListener;
    
    private NotificationManager notificationManager;
    
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
        configureLogger();
        proofListener = new MainProofListener();
        guiListener = new MainGUIListener();
        constraintListener = new MainConstraintTableListener();
        taskListener = new MainTaskListener();
        
        setMediator(new KeYMediator(this));
        
        initNotification();
        initProofList();
        layoutMain();
        initGoalList();
        initGUIProofTree();
        
        SwingUtilities.updateComponentTreeUI(this);
        ToolTipManager.sharedInstance().setDismissDelay(30000);
        setSize(1000, 750);
        addWindowListener(new MainListener());
        
    }
    
    private void initNotification() {
        if (!batchMode) {
            notificationManager = new NotificationManager(mediator);
        }
    }
    
    public static Main getInstance() {
        return getInstance(true);
    }
    
    public static Main getInstance(boolean visible) {
        if (instance == null) {
            instance = new Main("KeY -- Prover");
        }
        if (!instance.isVisible())
            instance.setVisible(visible); // XXX: enough?
        return instance;
    }
    
    
    public static void setStandalone(boolean b) {
        standalone = b;
    }
    
    
    public static void configureLogger() {
        if ((new File(LOGGER_CONFIGURATION)).exists())
            org.apache.log4j.PropertyConfigurator.configureAndWatch(LOGGER_CONFIGURATION, 1500);
        else {
            org.apache.log4j.BasicConfigurator.configure();
            Logger.getRootLogger().setLevel(org.apache.log4j.Level.ERROR);            
            DecisionProcedureSmtAuflia.configureLogger(org.apache.log4j.Level.DEBUG);  //Debugging of SMT Translation
        }
    }
    
    public String getPrcsVersion() {
        return INTERNAL_VERSION;
    }
    
    public void updateUI() {
        if (goalView != null)
            goalView.updateUI();
        if (proofView != null)
            proofView.updateUI();
        if (openGoalsView != null)
            openGoalsView.updateUI();
        if (userConstraintView != null)
            userConstraintView.updateUI();
        if (ruleView != null)
            ruleView.updateUI();
        if (proofListView != null)
            proofListView.updateUI();
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
        mediator.setSimplifier(ProofSettings.DEFAULT_SETTINGS
                .getSimultaneousUpdateSimplifierSettings().getSimplifier());
        
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
        
        autoModeAction = new AutoModeAction();
        openFileAction = new OpenFile();
        saveFileAction = new SaveFile();
        createUnitTestAction = new CreateUnitTestAction();

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

	userConstraintView = new UserConstraintView ();
	if ( mediator != null ) {
	    userConstraintView.setMediator(mediator);
	}

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
        toolBar.add(createDecisionProcedureButton());
        toolBar.addSeparator();
        
        JButton goalBackButton = new JButton("Goal Back");
        goalBackButton.setIcon(IconFactory.goalBackLogo(toolbarIconSize));
        goalBackButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setBack();
            }
        });
        
        toolBar.add(goalBackButton);
        toolBar.addSeparator();
        toolBar.add(reuseButton);

	toolBar.addSeparator();
        
        if (mediator.getProfile() instanceof JavaTestGenerationProfile) {
            toolBar.add(createUnitTestButton());
        }
        
        reuseButton.setEnabled(false);
        reuseButton.setToolTipText("Start proof reuse (when template available)");
        JMenuItem singleStepReuse = new JCheckBoxMenuItem("Single step");
        singleStepReuse.setSelected(false);
        singleStepReuse.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                mediator.setContinuousReuse(
                        !((JCheckBoxMenuItem)e.getSource()).isSelected());
            }
        });
        reusePopup.add(singleStepReuse);
        reuseButton.addMouseListener(new MouseAdapter() {
            public void mousePressed(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    reusePopup.show(e.getComponent(), e.getX(), e.getY());
                }
            }
        });
        toolBar.addSeparator();
        
        JToolBar fileOperations = new JToolBar("File Operations");
        fileOperations.add(createOpenFile());
        fileOperations.add(createOpenMostRecentFile());
        fileOperations.add(createSaveFile());
        
        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_R, ActionEvent.CTRL_MASK),
        "show_reuse_state");
        goalView.getActionMap().put("show_reuse_state", new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                mediator().showReuseState();
            }
        });

        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, ActionEvent.ALT_MASK),
        "show_reuse_cntd");
        goalView.getActionMap().put("show_reuse_cntd", new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                mediator().showPreImage();
            }
        });
        
        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_C, ActionEvent.CTRL_MASK), 
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
        
        getContentPane().add(clipBoardTextArea, BorderLayout.PAGE_START);
        getContentPane().add(toolBarPanel, BorderLayout.PAGE_START);
        
        // ============================================================
        // ==================== create tabbed pane ====================
        // ============================================================
        
        tabbedPane = new JTabbedPane();
        
        addTab("Proof", proofView, "The current state of the " + "proof as tree");
        
        addTab("Goals", openGoalsView, "The currently open goals");
        
        tabbedPane.addTab("User Constraint", null, userConstraintView,
        "Currently chosen metavariable instantiations");
        
        tabbedPane.addTab("Proof Search Strategy", null, strategySelectionView,
        "Select strategy for automated proof search");
        
        tabbedPane.addTab("Rules", null, new JScrollPane(ruleView), "All available rules");
        tabbedPane.setSelectedIndex(0);
        tabbedPane.setPreferredSize(new java.awt.Dimension(250, 440));
        tabbedPane.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP, ActionEvent.CTRL_MASK));
        tabbedPane.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, ActionEvent.CTRL_MASK));
        
        proofListView.setPreferredSize(new java.awt.Dimension(250, 100));
        paintEmptyViewComponent(proofListView, "Tasks");
        
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
        splitPane.setOneTouchExpandable(true);
        getContentPane().add(splitPane, BorderLayout.CENTER);
        
        statusLine = new MainStatusLine("<html>" + PARA + COPYRIGHT + PARA
                + "KeY is free software and comes with ABSOLUTELY NO WARRANTY."
                + " See Help | License.", getFont());
        getContentPane().add(statusLine, BorderLayout.SOUTH);
        setupInternalInspection();
    }
    

    /**
     * *********************** UGLY INSPECTION CODE **********************
     */
    private void setupInternalInspection() {
        goalView.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW ).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_Z, ActionEvent.CTRL_MASK), 
        "show_tree");
        goalView.getActionMap().put("show_tree", new AbstractAction() {
            
            public void actionPerformed(ActionEvent e) {
                System.err.println(sequentView.getMousePosInSequent().
                        getPosInOccurrence().posInTerm());
                
                Term t = 
                    sequentView.getMousePosInSequent().getPosInOccurrence().subTerm();
                System.err.println("****************** "+t.op().getClass());
                System.err.println(t.hashCode());
                t.tree();
                
//              if (t instanceof ProgramTerm) {
                de.uka.ilkd.key.java.visitor.JavaASTWalker w = 
                    new de.uka.ilkd.key.java.visitor.JavaASTWalker(
                            t.javaBlock().program()) {
                    protected void walk(ProgramElement node) {
                        if (node != root()) doAction(node);
                        if (node instanceof NonTerminalProgramElement) {
                            NonTerminalProgramElement nonTerminalNode = 
                                (NonTerminalProgramElement) node;
                            for (int i = 0; 
                            i<nonTerminalNode.getChildCount(); 
                            i++) {
                                walk(nonTerminalNode.getChildAt(i));
                            }	    
                        }
                    }
                    
                    protected void doAction(ProgramElement node) {
                        if (node instanceof Statement &&
                                !(node instanceof StatementBlock))
                            System.err.println(node.getClass()+":- "+node);
                        if (node instanceof 
                                de.uka.ilkd.key.java.statement.MethodFrame)
                            System.err.println(
                                    ((de.uka.ilkd.key.java.statement.MethodFrame)node).
                                    getExecutionContext());
                    }
                };
                w.start();               
            }
        });
    }
    
    private JButton createAutoModeButton() {
        return new JButton(autoModeAction);
    }
    
    private JComponent createOpenMostRecentFile() {
        final JButton button = new JButton();
        button.setAction(new OpenMostRecentFile());
        return button;
    }
    
    private JComponent createOpenFile() {
        final JButton button = new JButton();
        button.setAction(openFileAction);
        button.setText(null);
        return button;
    }
    
    private JComponent createSaveFile() {
        final JButton button = new JButton();
        button.setAction(saveFileAction);
        button.setText(null);
        return button;
    }



    private JButton createUnitTestButton(){
        testButton = new JButton();
        testButton.setAction(new CreateUnitTestAction());

        return testButton;
    }
    
    /** creates the toolbar button invoking decision procedures like ICS, Simplify */
    private JButton createDecisionProcedureButton() {
        String toolTipText = "Run "
            + ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
            .getDecisionProcedure();
        if ( ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useSMT_Translation() ) {
            toolTipText = "Run SMT Translation";
        }
        
        decisionProcedureButton = new JButton();
        decisionProcedureButton.setToolTipText(toolTipText);
        decisionProcedureButton.setText(toolTipText);
        
        // select icon
        if (ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useSimplify()) {
            decisionProcedureButton.setIcon(IconFactory.simplifyLogo(toolbarIconSize));
        } else if (ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useICS()) {
            decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
        } else if (ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useCVCLite()
                || ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useCVC3()
                || ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useSVC()
                || ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useYices()
                || ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().useSMT_Translation()) {
            // TODO: use different logos?!
            decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
        }
        
        decisionProcedureButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (!mediator.ensureProofLoaded()) return;
                new DecProcRunner(Main.this).run();
            }
        });
        
        return decisionProcedureButton;
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
    }
    
    private void setStatusLineImmediately(String s, int totalChars) {
        statusLine.reset();
        statusLine.setStatusText(s);
        getProgressMonitor().setMaximum(totalChars);
        statusLine.setProgressPanelVisible(true);
        // statusLine.setAbortButtonEnabled(false);
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


        recentFiles.store(RECENT_FILES_STORAGE);

        if (quit) {            
            mediator.fireShutDown(new GUIEvent(this));

            if (standalone) {
                // wait some seconds; give notification sound a bit time
                try {
                    Thread.sleep(1000);
                } catch(InterruptedException ie) {
                    Debug.out("Thread has been interrupted.");
                }
                System.out.println("Have a nice day.");
                System.exit(-1);
            }
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
            Iterator it = currentProof.getSettings().getChoiceSettings().getDefaultChoices()
            .values().iterator();
            String message = "Active Taclet Options:\n";
            while (it.hasNext()) {
                message += it.next().toString() + "\n";
            }
            final JTextComponent activeOptions = new JTextArea(message);
            activeOptions.setEditable(false);
            JOptionPane.showMessageDialog(Main.this, activeOptions, "Active Taclet Options",
                    JOptionPane.INFORMATION_MESSAGE);
        }
    }

    public void showSpecBrowser(){
	if(mediator.getProof() == null){
	    mediator.notify
	    (new GeneralFailureEvent("Please load a proof first"));
	}else{
	    JMLSpecBrowser.getJMLSpecBrowser(mediator);
	}
    }

    public void showDLSpecBrowser(){
	if(mediator.getProof() == null){
	    mediator.notify
	    (new GeneralFailureEvent("Please load a proof first"));
	}else{
	    JDialog fr = UsedMethodContractsList.getInstance(mediator());
	    fr.setVisible(true);
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
    
    /** opens configuration dialog for the simultaneous update simplifier */
    protected void configSimultaneousUpdateSimplifier() {
	SimultaneousUpdateSimplifierConfiguration config = 
	    new SimultaneousUpdateSimplifierConfiguration
	    (mediator(), 
	     ProofSettings.DEFAULT_SETTINGS.getSimultaneousUpdateSimplifierSettings());
	config.setVisible(true);
    }
    
    /**
     * opens a configuration dialog for the loaded libraries
     */
    protected void configLibraries() {
        LibrariesConfiguration config = 
            new LibrariesConfiguration
            (mediator(), 
             ProofSettings.DEFAULT_SETTINGS.getLibrariesSettings());
        config.setVisible(true);
    }
    
    protected void setBack() {
        mediator.setBack();
    }
    
    
    protected void makePrettyView() {
        if (mediator().ensureProofLoadedSilent()) {
            if (!PresentationFeatures.ENABLED) {
                mediator().getNotationInfo().setBackToDefault();
            } else {
                PresentationFeatures.modifyNotationInfo(mediator.getNotationInfo(), mediator
                        .func_ns());
            }
            mediator().getSelectedProof().updateProof();
            userConstraintView.updateTableDisplay(); // %%% HACK
        }
        
    }
    
    public JMLPOAndSpecProvider getJMLPOAndSpecProvider() {
        return new JMLEclipseAdapter(mediator);
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
    
    static java.awt.TextArea clipBoardTextArea = new java.awt.TextArea(
            "",10,10,java.awt.TextArea.SCROLLBARS_NONE) {
        public java.awt.Dimension getMaximumSize() {
            return new java.awt.Dimension(0,0);
        }
    };

 
    
    public static void copyHighlightToClipboard(SequentView view) {
        String s = view.getHighlightedText();
        // now CLIPBOARD
        java.awt.datatransfer.StringSelection ss = 
            new java.awt.datatransfer.StringSelection(s);
        clipBoardTextArea.getToolkit().getSystemClipboard().setContents(ss,ss);
        // now PRIMARY
        clipBoardTextArea.setText(s);
        clipBoardTextArea.selectAll();
    }
    
    protected JMenu createFileMenu() {
        JMenu fileMenu = new JMenu("File");
        fileMenu.setMnemonic(KeyEvent.VK_F);
        
        JMenuItem load = new JMenuItem();
        load.setAction(openFileAction);
        
        JMenuItem save = new JMenuItem();
        save.setAction(saveFileAction);
        
        registerAtMenu(fileMenu, load);
        registerAtMenu(fileMenu, save);
        
        JMenuItem tacletPOItem = new JMenuItem("Load Non-Axiom Lemma ...");
        tacletPOItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (mediator().ensureProofLoaded()) {
                    generateTacletPO();
                }
            }
        });
        registerAtMenu(fileMenu, tacletPOItem);
        
        JMenuItem exit = new JMenuItem("Exit");
        exit.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Q, ActionEvent.CTRL_MASK));
        exit.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                exitMain();
            }
        });
        
        addSeparator(fileMenu);
        
        recentFiles = new RecentFileMenu(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                loadProblem(new File(recentFiles.getAbsolutePath((JMenuItem) e.getSource())));
            }
        }, MAX_RECENT_FILES, null);
        
        recentFiles.load(RECENT_FILES_STORAGE);
        
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
        smaller.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, InputEvent.CTRL_DOWN_MASK));
        
        final JMenuItem larger = new JMenuItem("Larger");
        larger.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Config.DEFAULT.larger();
            }
        });
        larger.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_UP, InputEvent.CTRL_DOWN_MASK));
        
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
        pretty.setToolTipText("If ticked, infix notations are used.");
        pretty.setSelected(PresentationFeatures.ENABLED);
	pretty.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    PresentationFeatures.ENABLED=((JCheckBoxMenuItem)e.getSource()).
			isSelected();
		    makePrettyView();
		}});

	
	
	registerAtMenu(view, pretty);
	addSeparator(view);
		
	registerAtMenu(view, createFontSizeMenuEntry());
	
	final JMenuItem tacletOptionsView = new JMenuItem(TACLET_OPTIONS_MENU_STRING);

	tacletOptionsView.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_M, ActionEvent.CTRL_MASK));
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
        JMenuItem close = new JMenuItem("Abandon Task");
        close.setAccelerator(KeyStroke.getKeyStroke
                (KeyEvent.VK_W, ActionEvent.CTRL_MASK));
        close.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                closeTask();
            }});
        registerAtMenu(proof, close);	
        
        JMenuItem choiceItem = new JMenuItem("Show Active Taclet Options");
        choiceItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showActivatedChoices();
            }});
        registerAtMenu(proof, choiceItem);
        
        JMenuItem methodContractsItem = new JMenuItem("Show Used Specifications...");
        methodContractsItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
		JDialog fr = new UsedMethodContractsList
		    (mediator.getSelectedProof().getBasicTask(), mediator);
		fr.setVisible(true);
            }});
        registerAtMenu(proof, methodContractsItem);

        final JMenuItem statisticsInfo = new JMenuItem("Show Proof Statistics");
        
        statisticsInfo.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {                                    
                final Proof proof = mediator.getSelectedProof();
                if (mediator() != null && proof != null) {
                    
                    String stats = proof.statistics();
                    
                    int interactiveSteps = computeInteractiveSteps(proof.root());                  
                    
                    
                    stats += "Interactive Steps: " +interactiveSteps;
                    
                    JOptionPane.showMessageDialog(Main.this, 
                            stats,
                            "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
                }
            }

            private int computeInteractiveSteps(Node node) {
                int steps = 0;
                final IteratorOfNode it = node.childrenIterator();
                while (it.hasNext()) {
                  steps += computeInteractiveSteps(it.next());
                }
                
                if (node.getNodeInfo().getInteractiveRuleApplication()) {
                    steps++;
                }
                return steps;
            }
        });
        registerAtMenu(proof, statisticsInfo);

        return proof;
    }

    protected JMenu createOptionsMenu() {
	JMenu options = new JMenu("Options");
	options.setMnemonic(KeyEvent.VK_O);
	JMenuItem choiceItem = new JMenuItem("Default Taclet Options...");
	choiceItem.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_T, ActionEvent.CTRL_MASK));

	choiceItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    selectChoices();
		}});
	registerAtMenu(options, choiceItem);	

	JMenuItem updateSimplifierItem = new JMenuItem("Update Simplifier...");
	updateSimplifierItem.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_U, ActionEvent.CTRL_MASK));

	updateSimplifierItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    configSimultaneousUpdateSimplifier();
		}});
	registerAtMenu(options, updateSimplifierItem);	
    
	ButtonGroup decisionProcGroup = new ButtonGroup();
 
        JMenuItem librariesItem = new JMenuItem("Taclet Libraries...");
        librariesItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                configLibraries();
            }
        });
        registerAtMenu(options, librariesItem);
        
        setupDecisionProcedureGroup(decisionProcGroup);
        
        registerAtMenu(options, decisionProcedureOption);
        
        
        JMenuItem computeSpecificationOptions = 
            ComputeSpecificationView.createOptionMenuItems();
        registerAtMenu(options, computeSpecificationOptions);
        
        // GENERAL SETTINGS
        // minimize interaction
        final boolean stupidMode = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().stupidMode();
        final JMenuItem stupidModeOption = new
            JCheckBoxMenuItem("Minimize Interaction", stupidMode);
        mediator.setStupidMode(stupidMode);
        
        stupidModeOption.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
                mediator().setStupidMode(b);
                ProofSettings.DEFAULT_SETTINGS.
                getGeneralSettings().setStupidMode(b);
            }});
        
        registerAtMenu(options, stupidModeOption);
        
        
        // suggestive var names
        // currently removed to avoid confusion
        /*        
         final boolean suggestiveVarNames = 
         ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().suggestiveVarNames();
         final JMenuItem suggVarNamesOption = 
         new JCheckBoxMenuItem("Suggestive names for aux vars", 
         suggestiveVarNames);
         VariableNamer.setSuggestiveEnabled(suggestiveVarNames);
         
         suggVarNamesOption.addActionListener(new ActionListener() {
         public void actionPerformed(ActionEvent e) {
         boolean b = ((JCheckBoxMenuItem)e.getSource()).isSelected();
         VariableNamer.setSuggestiveEnabled(b);
         ProofSettings.DEFAULT_SETTINGS.
         getGeneralSettings().setSuggestiveVarNames(b);
         }});
         
         registerAtMenu(options, suggVarNamesOption);
         */
               
			
	addSeparator(options);

        final boolean dndDirectionSensitivity = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isDndDirectionSensitive();
        final JMenuItem dndDirectionSensitivityOption =
            new JCheckBoxMenuItem("DnD Direction Sensitive", dndDirectionSensitivity);
        dndDirectionSensitivityOption.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                boolean b = ((JCheckBoxMenuItem)e.getSource()).isSelected();           
                ProofSettings.DEFAULT_SETTINGS.
                getGeneralSettings().setDnDDirectionSensitivity(b);           
        }});
        
        registerAtMenu(options, dndDirectionSensitivityOption);        
        
	// sound settings
	final boolean soundNotification = 
	    ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().soundNotification();
	final JMenuItem soundNotificationOption =
	    new JCheckBoxMenuItem("Sound", soundNotification);
	if (notificationManager!=null) {
            notificationManager.setDefaultNotification(soundNotification);
        }
	soundNotificationOption.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
	        boolean b = ((JCheckBoxMenuItem)e.getSource()).isSelected();	       
	        if (notificationManager!=null) {
                    notificationManager.setDefaultNotification(b);                
	        }
	        ProofSettings.DEFAULT_SETTINGS.
	        getGeneralSettings().setSoundNotification(b);	        
        }});
	
	registerAtMenu(options, soundNotificationOption);


	// proof assistant
	final JMenuItem assistantOption = new JCheckBoxMenuItem
	    ("Proof Assistant", 
	     ProofSettings.DEFAULT_SETTINGS.
	     getGeneralSettings().proofAssistantMode());

	final ProofAssistantController assistant = new ProofAssistantController
	    (mediator, 
	     ProofSettings.DEFAULT_SETTINGS.getGeneralSettings(),
	     new ProofAssistantAI(), new ProofAssistant());

 	// listen to the state of the assistant in order to hold the
 	// item and state consistent
	assistant.addChangeListener(new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
	        final boolean assistentEnabled = 
                    ((ProofAssistantController)e.getSource()).getState();
	        assistantOption.setSelected(assistentEnabled);
	        // setSelected does not trigger an action event so we have
	        // to make the change explicitly permanent
	        ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().
	        setProofAssistantMode(assistentEnabled);
	    }
	});

	assistantOption.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().
		    setProofAssistantMode
		    (((JCheckBoxMenuItem)e.getSource()).isSelected());
	    }});

	registerAtMenu(options, assistantOption);
	        
        return options;
    }

    /**
     * @param decisionProcGroup
     */
    private void setupDecisionProcedureGroup(ButtonGroup decisionProcGroup) {
        simplifyButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useSimplify());
        simplifyButton.setIcon(IconFactory.simplifyLogo(15));
        decisionProcGroup.add(simplifyButton);
        decisionProcedureOption.add(simplifyButton);
        
        DecisionProcButtonListener decisionProcButtonListener = new DecisionProcButtonListener();
        simplifyButton.addActionListener(decisionProcButtonListener);
        
        icsButton.setIcon(IconFactory.icsLogo(15));
        icsButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useICS());
        decisionProcGroup.add(icsButton);
        decisionProcedureOption.add(icsButton);
        icsButton.addActionListener(decisionProcButtonListener);
        
        cvc3Button.setIcon(IconFactory.icsLogo(15));
        cvc3Button.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useCVC3());
        decisionProcGroup.add(cvc3Button);
        decisionProcedureOption.add(cvc3Button);
        cvc3Button.addActionListener(decisionProcButtonListener);
        
        
        cvcLiteButton.setIcon(IconFactory.icsLogo(15));
        cvcLiteButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useCVCLite());
        decisionProcGroup.add(cvcLiteButton);
        decisionProcedureOption.add(cvcLiteButton);
        cvcLiteButton.addActionListener(decisionProcButtonListener);
        
        svcButton.setIcon(IconFactory.icsLogo(15));
        svcButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useSVC());
        decisionProcGroup.add(svcButton);
        decisionProcedureOption.add(svcButton);
        svcButton.addActionListener(decisionProcButtonListener);
        
        yicesButton.setIcon(IconFactory.icsLogo(15));
        yicesButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useYices());
        decisionProcGroup.add(yicesButton);
        decisionProcedureOption.add(yicesButton);
        yicesButton.addActionListener(decisionProcButtonListener);
        
        smtButton.setIcon(IconFactory.icsLogo(15));
        smtButton.setSelected(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                .useSMT_Translation());
        decisionProcGroup.add(smtButton);
        decisionProcedureOption.add(smtButton);
        smtButton.addActionListener(decisionProcButtonListener);
        
        // Add option for quantifier translation
        final boolean useQuantifiers = ProofSettings.DEFAULT_SETTINGS
                                       .getDecisionProcedureSettings().useQuantifiers();
        smtUseQuantifiersOption = new JCheckBoxMenuItem("Translate quantifiers (SMT)",
                                                        useQuantifiers);
        decisionProcedureOption.add(smtUseQuantifiersOption);
        smtUseQuantifiersOption.addActionListener(decisionProcButtonListener);
        
        // Add the options for SMT benchmark archiving
        decisionProcedureOption.addSeparator();
        final boolean benchmarkArchiving = ProofSettings.DEFAULT_SETTINGS
                                           .getDecisionProcedureSettings().doBenchmarkArchiving();
        smtBenchmarkArchivingOption = new JCheckBoxMenuItem("Archive SMT benchmarks",
                                                            benchmarkArchiving);
        decisionProcedureOption.add(smtBenchmarkArchivingOption);
        smtBenchmarkArchivingOption.addActionListener(decisionProcButtonListener);
                
        final boolean zipProblemDir = ProofSettings.DEFAULT_SETTINGS
                                      .getDecisionProcedureSettings().doZipProblemDir();
        smtZipProblemDirOption = new JCheckBoxMenuItem("Zip problem dir into archive", zipProblemDir);
        decisionProcedureOption.add(smtZipProblemDirOption);
        smtZipProblemDirOption.addActionListener(decisionProcButtonListener);
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
    
    protected JMenu createToolsMenu() {
	JMenu tools = new JMenu("Tools");
	tools.setMnemonic(KeyEvent.VK_T);
	getJMenuBar().add(tools);

	JMenuItem extractSpecification = new JMenuItem("Extract Specification");
	extractSpecification.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_E, ActionEvent.CTRL_MASK));

	extractSpecification.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if (mediator().ensureProofLoaded()) {
			//@internal we don't want to block UI just
			//because we are about to calculate a lot of
			//things, now. Also the interactive prover
			//might want to run during the execution of
			//ComputeSpecification
			new Thread(new Runnable() {
				public void run() {
				    ComputeSpecificationView.show(mediator());
				}
			    }).start();
		    }
		}
	    });
	tools.add(extractSpecification);

	JMenuItem specificationBrowser = 
	    new JMenuItem("JML Specification Browser...");
	specificationBrowser.setAccelerator(KeyStroke.getKeyStroke
					    (KeyEvent.VK_J, 
					     ActionEvent.CTRL_MASK));
	specificationBrowser.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    showSpecBrowser();
		}});
	registerAtMenu(tools, specificationBrowser);


	JMenuItem dlSpecificationBrowser = 
	    new JMenuItem("DL Specification Browser...");
	dlSpecificationBrowser.setAccelerator(KeyStroke.getKeyStroke
					    (KeyEvent.VK_L, 
					     ActionEvent.CTRL_MASK));
	dlSpecificationBrowser.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    showDLSpecBrowser();
		}});
	registerAtMenu(tools, dlSpecificationBrowser);
        
        JMenuItem nonInterference = new JMenuItem("Check Non-Interference");
        nonInterference.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                BasicTask[] selProofs = proofList.getAllSelectedBasicTasks();
                if (selProofs.length==2) {
                    new NonInterferenceCheck(selProofs).run();
                } else {
                    mediator().popupWarning(
                            "Please select 2 proofs", "Non-Interference Check");
                }
            }
        });
        
        tools.add(nonInterference);
        
        JMenuItem testItem = new JMenuItem();
        testItem.setAction(createUnitTestAction);
        
        tools.add(testItem);
        
        return tools;
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
        menuBar.add(createToolsMenu());
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
        goalView.setViewportView(goalViewPane);
        goalView.setBorder(new TitledBorder(borderTitle));
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
        SequentPrintFilter filter =
            new ConstraintSequentPrintFilter ( sequent,
                    mediator ().getUserConstraint ()
                    .getConstraint () );
        
        
        final LogicPrinter printer;
        
        if (mediator.getProfile() instanceof HoareProfile) {            
            printer = new HoareLogicPrettyPrinter(new ProgramPrinter(null), 
                    mediator().getNotationInfo(),
                    mediator.getServices());
        } else {
            printer = new LogicPrinter(new ProgramPrinter(null), 
                    mediator().getNotationInfo(),
                    mediator.getServices());
        }         
        sequentView.setPrinter(printer, filter, null);
        sequentView.printSequent();
        
        updateGoalView("Current Goal", sequentView);
    }
    
    
    public static KeYFileChooser getFileChooser(String title) {
        if (fileChooser == null) {
            fileChooser = new KeYFileChooser();
        }
        fileChooser.setDialogTitle(title);
        fileChooser.prepare();
        return fileChooser;
    }
    
    /** saves a proof */
    protected void saveProof() {
        KeYFileChooser jFC = getFileChooser("Choose filename to save proof");
        boolean saved = jFC.showSaveDialog(this);
        if (saved) {
            saveProof(jFC.getSelectedFile());
        }
    }
    
    protected void saveProof(String proofFile) {
        saveProof(new File(proofFile));
    }
    
    protected void saveProof(File proofFile) {
        String filename = proofFile.getAbsolutePath();    
        ProofSaver saver;
        if (filename.endsWith(".tex"))
            saver = new ProofSaverLatex(this, filename);
        else saver = new ProofSaver(this, filename);
        String errorMsg = saver.save();
        
        if (errorMsg != null) {
            notify(new GeneralFailureEvent
                    ("Saving Proof failed.\n Error: " + errorMsg));
        }
    }
    
    protected void loadProblem(File file) {
	recentFiles.addRecentFile(file.getAbsolutePath());
        if(unitKeY!=null){
            unitKeY.recent.addRecentFile(file.getAbsolutePath());
        }
        new ProblemLoader(file, this, mediator.getProfile()).run();
    }
    
    protected void closeTask() {
	final Proof proof = mediator.getProof();
	if (proof != null) {
	    final TaskTreeNode rootTask = 
		proof.getBasicTask().getRootTask();	
	    proofList.removeTask(rootTask);   
	    
            ((ProofTreeView)proofView.getComponent(0)).removeProofs(rootTask.allProofs());
	}
    }
    
    
    public void closeTaskWithoutIntercation() {
        final Proof proof = mediator.getProof();
        if (proof != null) {
            final TaskTreeNode rootTask = 
                proof.getBasicTask().getRootTask();     
            proofList.removeTaskWithoutInteraction(rootTask);   
            
            ((ProofTreeView)proofView.getComponent(0)).removeProofs(rootTask.allProofs());
        }
    }
    
    protected void generateTacletPO () {
        final KeYFileChooser localFileChooser = getFileChooser ("Choose file to "
                +"load taclets "
                +"from ...");
        boolean loaded = localFileChooser.showOpenDialog ( Main.this );
        if (!loaded)
            return;
        
        final File file = localFileChooser.getSelectedFile ();
        
        new TacletSoundnessPOLoader(file, this).run();
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
        KeYMediator localMediator = mediator();
        localMediator.setProof(proof);
        return proof;
    }
    
    private java.util.Hashtable doNotEnable;
    
    private void setToolBarDisabled() {
        doNotEnable = new java.util.Hashtable(10);
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
    
    /**
     * Loads the last opened file
     */
    private final class OpenMostRecentFile extends AbstractAction {
        
        public OpenMostRecentFile() {
            putValue(SMALL_ICON, IconFactory.openMostRecent(toolbarIconSize));
            putValue(SHORT_DESCRIPTION, "Load last opened file.");
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
     * Opens a file dialog allowing to select the file to be loaded
     */
    private final class OpenFile extends AbstractAction {
        public OpenFile() {
            putValue(NAME, "Load ...");
            putValue(SMALL_ICON, IconFactory.openKeYFile(toolbarIconSize));
            putValue(SHORT_DESCRIPTION, "Browse and load problem or proof files.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_O, ActionEvent.CTRL_MASK));
            
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
     * Saves the current selected proof.
     */
    private final class SaveFile extends AbstractAction {
        
        public SaveFile() {
            putValue(NAME, "Save ...");
            putValue(SMALL_ICON, IconFactory.saveFile(toolbarIconSize));
            putValue(SHORT_DESCRIPTION, "Save current proof.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_S, ActionEvent.CTRL_MASK));
            
            setEnabled(mediator.getProof() != null);
            
            mediator.addKeYSelectionListener(new KeYSelectionListener() {
                /** focused node has changed */
                public void selectedNodeChanged(KeYSelectionEvent e) {
                }
                
                /**
                 * the selected proof has changed. Enable or disable action depending whether a proof is
                 * available or not
                 */ 
                public void selectedProofChanged(KeYSelectionEvent e) {
                    setEnabled(e.getSource().getSelectedProof() != null);
                }
            });
        }
        
        public void actionPerformed(ActionEvent e) {
            if (mediator().ensureProofLoaded()) {
                saveProof();
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
            if(testStandalone){
                visible = false;
                setVisible(false);
            }else{
                exitMain();
            }
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
                Main.this.userConstraintView.setEnabled(false);
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
                Main.this.userConstraintView.setEnabled(true);
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
            try {
                goal = mediator().getSelectedGoal();
            } catch(IllegalStateException e) { // there is no proof (yet)
                return;
            }
            if ( goal != null &&
                    !mediator.getUserConstraint ().displayClosed ( goal.node () ) ){
                printSequentView(goal.sequent());
            } else {
                NonGoalInfoView innerNodeView = 
                    new NonGoalInfoView(mediator().getSelectedNode(), 
                            mediator());
                updateGoalView("Inner Node", innerNodeView);
            }
        }
    }
    
    class MainProofListener implements AutoModeListener, 
    KeYSelectionListener,
    SettingsListener {
        
        Logger logger = Logger.getLogger("key.threading");
        
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
            
            if ( userConstraint != null )
                userConstraint
                .removeConstraintTableListener ( constraintListener );
            
            userConstraint = (proof != null) ? proof.getUserConstraint() :
                null;
            
            if ( userConstraint != null )
                userConstraint
                .addConstraintTableListener ( constraintListener );
            setProofNodeDisplay();
            makePrettyView();
            // update label of autoModeButton and update decproc options list
            updateDecisionProcedureButton();
            DecisionProcedureSettings currentSetting = 
                ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings();
            if ( proof != null ) {
                currentSetting = proof.getSettings().getDecisionProcedureSettings();
            }    
            simplifyButton.setSelected( currentSetting.useSimplify() );
            icsButton.setSelected( currentSetting.useICS() );
            cvcLiteButton.setSelected( currentSetting.useCVCLite() );
            cvc3Button.setSelected( currentSetting.useCVC3() );
            svcButton.setSelected( currentSetting.useSVC() );
            yicesButton.setSelected( currentSetting.useYices() );
            smtButton.setSelected( currentSetting.useSMT_Translation() );
            smtUseQuantifiersOption.setSelected( currentSetting.useQuantifiers() );
            smtBenchmarkArchivingOption.setSelected( currentSetting.doBenchmarkArchiving() );
            smtZipProblemDirOption.setSelected( currentSetting.doZipProblemDir() );
                        
            // Inform the decproc classes that the selected proof has changed!
            DecisionProcedureSmtAuflia.fireSelectedProofChanged( proof );                       
        }
        
        /**
         * invoked if automatic execution has started
         */
        public synchronized void autoModeStarted(ProofEvent e) {
            logger.warn("Automode started");
            disableCurrentGoalView = true;
            mediator().removeKeYSelectionListener(proofListener);
            freezeExceptAutoModeButton();
        }
        
        /**
         * invoked if automatic execution has stopped
         */
        public synchronized void autoModeStopped(ProofEvent e) {
            logger.warn("Automode stopped");
            if (logger.isDebugEnabled()) {
                logger.debug("From " + Debug.stackTrace());
            }
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
    
    class DecisionProcButtonListener implements ActionListener {
        public void actionPerformed(ActionEvent e) {
            Proof currentProof = mediator.getProof();
            ProofSettings currentSettings = ProofSettings.DEFAULT_SETTINGS;
            if (currentProof != null)
                currentSettings = currentProof.getSettings();
            
            if (e.getSource() == simplifyButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                        DecisionProcedureSettings.SIMPLIFY);
            } else if (e.getSource() == icsButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                        DecisionProcedureSettings.ICS);
            } else if (e.getSource() == cvcLiteButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                        DecisionProcedureSettings.CVCLite);
            } else if (e.getSource() == cvc3Button) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                        DecisionProcedureSettings.CVC3);
            } else if (e.getSource() == svcButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                            DecisionProcedureSettings.SVC);
            } else if (e.getSource() == yicesButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                        DecisionProcedureSettings.YICES);
            } else if (e.getSource() == smtButton) {
                currentSettings.getDecisionProcedureSettings().setDecisionProcedure(
                            DecisionProcedureSettings.SMT);
            } else if ( e.getSource() == smtUseQuantifiersOption) {
                boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
                currentSettings.getDecisionProcedureSettings().setUseQuantifier(b);
                ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().setUseQuantifier(b);
            } else if ( e.getSource() == smtBenchmarkArchivingOption) {
                boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
                currentSettings.getDecisionProcedureSettings().setDoBenchmarkArchiving(b);
                ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings()
                    .setDoBenchmarkArchiving(b);
            } else if ( e.getSource() == smtZipProblemDirOption) {
                boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
                currentSettings.getDecisionProcedureSettings().setDoZipProblemDir(b);
                ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().setDoZipProblemDir(b);
            }
            updateDecisionProcedureButton();
	    if (currentProof != null){
		ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().setDecisionProcedure(
                    currentSettings.getDecisionProcedureSettings().getDecisionProcedure());
	    }
        }
    }
    
    public void updateDecisionProcedureButton() {
        Proof currentProof = mediator.getProof();
        DecisionProcedureSettings decSettings = (currentProof == null) ? ProofSettings.DEFAULT_SETTINGS
                .getDecisionProcedureSettings()
                : currentProof.getSettings().getDecisionProcedureSettings();
                if (decSettings.useSimplify()) {
                    decisionProcedureButton.setIcon(IconFactory.simplifyLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run Simplify");
                    decisionProcedureButton.setText("Run Simplify");
                } else if (decSettings.useICS()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run ICS");
                    decisionProcedureButton.setText("Run ICS");
                } else if (decSettings.useCVCLite()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run CVCLite");
                    decisionProcedureButton.setText("Run CVCLite");
                } else if (decSettings.useCVC3()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run CVC3");
                    decisionProcedureButton.setText("Run CVC3");
                } else if (decSettings.useSVC()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run SVC");
                    decisionProcedureButton.setText("Run SVC");
                } else if (decSettings.useYices()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run Yices");
                    decisionProcedureButton.setText("Run Yices");
                } else if (decSettings.useSMT_Translation()) {
                    decisionProcedureButton.setIcon(IconFactory.icsLogo(toolbarIconSize));
                    decisionProcedureButton.setToolTipText("Run SMT Translation");
                    decisionProcedureButton.setText("Run SMT Translation");
                }
    }
    
    class MainConstraintTableListener implements ConstraintTableListener {
        public void constraintChanged(ConstraintTableEvent e) {
            setProofNodeDisplay();
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
        
        public void taskFinished() {
            final MainStatusLine sl = getStatusLine();
            sl.reset();
        }
    }
    
    public static void evaluateOptions(String[] opt) {
	int index = 0;
        boolean loadJavaProfile = false;
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
		    jmlSpecs = false;
		} else if (opt[index].equals("AUTO")) {
		    batchMode = true;
		} else if (opt[index].equals("TESTING") || opt[index].equals("UNIT")) {
                    if(opt[index].equals("TESTING")){
                        testStandalone = true;
                        visible = false;
                    }
                    System.out.println("VBT optimizations enabled ...");                    
                    
                    final Profile p = new JavaTestGenerationProfile(null);
                    
                    if (index + 1 < opt.length && 
                            opt[index + 1].toUpperCase().equals("LOOP")) {
                        p.setSelectedGoalChooserBuilder(BalancedGoalChooserBuilder.NAME);
                        System.out.println("Balanced loop unwinding ...");
                        index ++;
                    }
                    ProofSettings.DEFAULT_SETTINGS.setProfile(p);
                    p.updateSettings(ProofSettings.DEFAULT_SETTINGS);
                    testMode = true;
		} else if (opt[index].equals("DEBUGGER")) {                                     
                    System.out.println("Symbolic Execution Debugger Mode enabled ...");                                        
                    final Profile p = new DebuggerProfile(null);                    
                    if (index + 1 < opt.length && 
                            opt[index + 1].equals("LOOP")) {
                        p.setSelectedGoalChooserBuilder(BalancedGoalChooserBuilder.NAME);
                        //System.out.println("Balanced loop unwinding ...");
                        index ++;
                    }
                    ProofSettings.DEFAULT_SETTINGS.setProfile(p);
                    p.updateSettings(ProofSettings.DEFAULT_SETTINGS);
                    testMode = true;
                } else if (opt[index].equals("FOL")) {                     
                    ProofSettings.DEFAULT_SETTINGS.setProfile(new PureFOLProfile());
                } else if (opt[index].equals("JAVA")) {                    
                    loadJavaProfile = true;
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
            statisticsFile = opt[index + 1];
            ++index;
        } else {
		    printUsageAndExit ();
		}		
	    }
	    index++;
	}	
        if (!loadJavaProfile) {
            // ok hoare
            ProofSettings.DEFAULT_SETTINGS.setProfile(new HoareProfile());
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

    private static void printUsageAndExit() {
        System.out.println("File not found or unrecognized option.\n");
        System.out.println("Possible parameters are (* = default): ");
        System.out.println("  no_debug        : disables debug mode (*)");
        System.out.println("  debug           : enables debug mode");
        System.out.println("  no_assertion    : disables assertions");
        System.out.println("  assertion       : enables assertions (*)");
        System.out.println("  no_jmlspecs     : disables parsing JML specifications");
        System.out.println("  unit [loop]     : unit test generation mode (optional argument loop to " +
                            "enable balanced loop unwinding)");
        System.out.println("  auto	          : start prove procedure after initialisation");
        System.out.println("  testing         : starts the prover with a simple test generation oriented user interface");
        System.out.println("  print_statistics <filename>" );
        System.out.println("                  : in auto mode, output nr. of rule applications and time spent");
        System.out.println("  fol             : use FOL profile (no program or update rules)");
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
    class BlockingGlassPane extends JComponent {
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
    class GlassPaneListener extends MouseInputAdapter {
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
    
    private final class CreateUnitTestAction extends AbstractAction {
        final Icon icon = IconFactory.junitLogo(toolbarIconSize);
        
        public CreateUnitTestAction() {            
            putValue(NAME, "Create Unittests");          
            putValue(Action.SHORT_DESCRIPTION, "Create JUnit test cases from proof.");
            putValue(Action.SMALL_ICON, icon);            
            
            setEnabled(mediator.getSelectedProof() != null);
            
            mediator.addKeYSelectionListener(new KeYSelectionListener() {
                /** focused node has changed */
                public void selectedNodeChanged(KeYSelectionEvent e) {}
                
                /**
                 * the selected proof has changed. Enable or disable action depending whether a
                 * proof is available or not
                 */ 
                public void selectedProofChanged(KeYSelectionEvent e) {
                    setEnabled(e.getSource().getSelectedProof() != null);
                }
            });             
        }
        
        public void actionPerformed(ActionEvent e) {
            MethodSelectionDialog.getInstance(mediator);
        }
    }
    
    private final class AutoModeAction extends AbstractAction {
        
        final Icon startLogo = 
            IconFactory.autoModeStartLogo ( toolbarIconSize );
        final Icon stopLogo = 
            IconFactory.autoModeStopLogo ( toolbarIconSize );
        
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
		ListOfGoal newGoals = e.getGoals();
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
        
        public AutoModeAction() {
            putValue("hideActionText", Boolean.TRUE);
            putValue(Action.SHORT_DESCRIPTION, AUTO_MODE_TEXT);
            putValue(Action.SMALL_ICON, startLogo);
            
            associatedProof = mediator.getProof();        
            
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
            else
                mediator().stopAutoMode();
        }
        
    }
    
    public void loadCommandLineFile() {
        if (fileNameOnStartUp != null) {
            loadProblem(new File(fileNameOnStartUp));
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
        if(testStandalone){
            key.unitKeY = new UnitTestGeneratorGui(key);
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
    
    private final static class UnitTestGeneratorGui extends JFrame {
        
        protected final Main main;
        final protected KeYMediator mediator;
        private int toolbarIconSize = 15;
        private static UnitTestGeneratorGui testGui;
        private boolean openDialog=false;
        private RecentFileMenu recent=null;
        private JButton run;
        private JFrame proofList;
        private HashMap test2model;
        private boolean autoMode = false;
        
        public static final String AUTO_MODE_TEXT = "Create Tests";
        
        public UnitTestGeneratorGui(Main main){
            super("KeY Unit Test Generator");
            this.main = main;
            mediator = main.mediator();
            test2model = new HashMap();
            setIconImage(IconFactory.keyLogo());
            createProofList();
            layoutGui();
            setLocation(70, 70);
            addWindowListener(new UnitTestGeneratorGuiListener());
            pack();     
            Dimension d = getSize();
            d.setSize(400, (int) d.getHeight()+3);
            setSize(d);
            setVisible(true);
            testGui = this;
        }
        
       protected void createProofList(){
            proofList = new JFrame("Test Requirements");
            proofList.getContentPane().add(main.proofListView);
            proofList.setSize(400, 170);
            proofList.addWindowListener(new WindowAdapter(){
                public void windowClosing(WindowEvent e) {
                    proofList.setVisible(false);
                }
            });
            proofList.setVisible(true);            
        }
        
        protected void layoutGui(){
            setJMenuBar(new JMenuBar());
            getJMenuBar().add(createFileMenu());
            getJMenuBar().add(createToolsMenu());
            getJMenuBar().add(createOptionsMenu());
            getJMenuBar().add(Box.createHorizontalGlue());
            getJMenuBar().add(main.createHelpMenu());
            run = new JButton(new AutoModeAction());
            getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
            JPanel buttonPanel = new JPanel();
            buttonPanel.add(run);
            JPanel sliderPanel = new JPanel();
            sliderPanel.setLayout(new BoxLayout(sliderPanel, BoxLayout.Y_AXIS));
            sliderPanel.add(new MaxRuleAppSlider (mediator));
            buttonPanel.add(sliderPanel);
            buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
            getContentPane().add(buttonPanel);
            MainStatusLine msl = main.getStatusLine();
            getContentPane().add(msl);
        }
        
        class UnitTestGeneratorGuiListener extends WindowAdapter {
            public void windowClosing(WindowEvent e) {
                main.exitMain();             
            }
        }  
        
        private void runTest(String testPath, String modelDir) throws IOException{
            String testDir = testPath.substring(0, testPath.lastIndexOf(File.separator))+modelDir;
            String test = testPath.substring(testPath.lastIndexOf(File.separator)+1);
            Runtime.getRuntime().exec("cp "+testPath+" "+testDir);
            File testDirFile = new File(testDir);
            Runtime rt = Runtime.getRuntime();
            Process compile = rt.exec("javac "+test, null, testDirFile);
            String compileError = read(compile.getErrorStream()).trim();
            if(!"".equals(compileError)){
                throw new RuntimeException(compileError);
            }
            
            Process runJUnit = rt.exec("java junit.swingui.TestRunner "+
                    test.substring(0, test.lastIndexOf(".")), null, testDirFile);
            String junitError = read(runJUnit.getErrorStream());
            if(!"".equals(junitError)){
                throw new RuntimeException(junitError);
            }   
        }
        
        private void createTestSelectionWindow(){
            JDialog tsw = new JDialog(this, "Select Test Case");
            tsw.getContentPane().setLayout(new BoxLayout(tsw.getContentPane(), 
                 BoxLayout.Y_AXIS));
            final JList testList = new JList();
            testList.setListData(bubbleSortTests(createTestArray()));
            
            JScrollPane testListScroll = new
                JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
                        JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            testListScroll.getViewport().setView(testList);
            testListScroll.setBorder(
                    new TitledBorder("Created Tests"));
            testListScroll.setMinimumSize(new java.awt.Dimension(150, 400));
            tsw.getContentPane().add(testListScroll);
            
            JButton test = new JButton("Run Test");
            test.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if(testList.getSelectedValue() == null){
                        JOptionPane.showMessageDialog(
                            null, "You must select a test first!",
                            "No Test Selected", 
                            JOptionPane.ERROR_MESSAGE);
                    }else{
                        TestAndModel tam = (TestAndModel) testList.getSelectedValue();
                        try{
                            runTest(tam.test, tam.model);
                        }catch(Exception exc){
                            ExtList l = new ExtList();
                            l.add(exc);
                            new ExceptionDialog(testGui, l);    
                        }
                    }
                }
            });
            tsw.getContentPane().add(test);
            tsw.pack();
            tsw.setVisible(true);
        }
        
        private Object[] bubbleSortTests(Object[] tams){
            boolean sorted = false;
            while(!sorted){
                sorted = true;
                for(int i=0; i<tams.length-1; i++){
                    if(tams[i].toString().compareTo(tams[i+1].toString())>0){
                        Object temp = tams[i];
                        tams[i] = tams[i+1];
                        tams[i+1] = temp;
                        sorted = false;
                    }
                }
            }
            return tams;
        }
        
        private Object[] createTestArray(){
            Iterator it = test2model.entrySet().iterator();
            Vector v = new Vector();
            while(it.hasNext()){
                Map.Entry e = (Map.Entry) it.next();
                String test = ((StringBuffer) e.getKey()).toString();
                String model = (String) e.getValue();
                while(!"".equals(test.trim())){
                    v.add(new TestAndModel(test.substring(0, test.indexOf(" ")), model));
                    test = test.substring(test.indexOf(" ")+1);
                }
            }
            return v.toArray();
        }
        
        class TestAndModel{
            public String test;
            public String model;
            
            public TestAndModel(String test, String model){
                this.test = test;
                this.model = model;
            }
            
            public String toString(){
                return test;
            }
        }
        
        /** Read the input until end of file and return contents in a
         * single string containing all line breaks. */
        protected String read ( InputStream in ) throws IOException {
            String lineSeparator = System.getProperty("line.separator");
            BufferedReader reader = new BufferedReader
                (new InputStreamReader(in));
            StringBuffer sb = new StringBuffer();
            String line;
            while ((line = reader.readLine()) != null) {
                sb.append(line).append(lineSeparator);
            }
            return sb.toString();
        }
        
        protected JMenu createFileMenu() {
            JMenu fileMenu = new JMenu("File");
            fileMenu.setMnemonic(KeyEvent.VK_F);
            
            JMenuItem load = new JMenuItem();
            load.setAction(openFileAction);
       
            fileMenu.add(load);
   
            JMenuItem exit = new JMenuItem("Exit");
            exit.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Q, ActionEvent.CTRL_MASK));
            exit.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    main.exitMain();
                }
            });
            
            fileMenu.addSeparator();
            
            recent = new RecentFileMenu(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    main.loadProblem(new File(recent.getAbsolutePath((JMenuItem) e.getSource())));
                }
            }, MAX_RECENT_FILES, null);
            
            recent.load(RECENT_FILES_STORAGE);
            
            fileMenu.add(recent.getMenu());
            
            fileMenu.addSeparator();
            fileMenu.add(exit);
            return fileMenu;
        }
      
        protected JMenu createToolsMenu() {
            JMenu toolsMenu = new JMenu("Tools");
            JMenuItem specificationBrowser = 
                new JMenuItem("JML Specification Browser...");
            specificationBrowser.setAccelerator(KeyStroke.getKeyStroke
                                                (KeyEvent.VK_J, 
                                                        ActionEvent.CTRL_MASK));
            specificationBrowser.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        main.showSpecBrowser();
                    }});
            toolsMenu.add(specificationBrowser);
            
            final JMenuItem showProver = new JMenuItem("Show Prover",
                    IconFactory.keyLogo(toolbarIconSize, toolbarIconSize));
            showProver.setAccelerator(KeyStroke.getKeyStroke
                    (KeyEvent.VK_P, ActionEvent.CTRL_MASK));
            showProver.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    Main.visible = !Main.visible;
                    main.setVisible(Main.visible);
                    showProver.setText(Main.visible ? "Hide Prover" : "Show Prover");
                }});
            toolsMenu.add(showProver);
            
            final JMenuItem runTest = new JMenuItem("Run Created Tests", 
                    IconFactory.junitLogo(toolbarIconSize));
            runTest.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    createTestSelectionWindow();    
                }});
            toolsMenu.add(runTest);
            
            final JMenuItem showRequirements = new JMenuItem("Hide Test Requirements");
            showRequirements.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    proofList.setVisible(!proofList.isVisible());
                    showRequirements.setText(proofList.isVisible() ? 
                            "Hide Test Requirements" : "Show Test Requirements"); 
                }});
            toolsMenu.add(showRequirements);
            
            toolsMenu.addMenuListener(new MenuListener() {
                public void menuCanceled(MenuEvent arg0) {}

                public void menuDeselected(MenuEvent arg0) {}

                public void menuSelected(MenuEvent arg0) {
                    showProver.setText(Main.visible ? "Hide Prover" : "Show Prover"); 
                    showRequirements.setText(proofList.isVisible() ? 
                            "Hide Test Requirements" : "Show Test Requirements"); 
                }});
            return toolsMenu;
        }
        
        protected JMenu createOptionsMenu() {
            JMenu options = new JMenu("Options");
            options.setMnemonic(KeyEvent.VK_O);
            JMenuItem choiceItem = new JMenuItem("Taclet options defaults");
            choiceItem.setAccelerator(KeyStroke.getKeyStroke
                    (KeyEvent.VK_T, ActionEvent.CTRL_MASK));

            choiceItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    main.selectChoices();
                }});
            options.add(choiceItem);    

            ButtonGroup decisionProcGroup = new ButtonGroup();
     
            JMenu decisionProcedureOption = new JMenu("Decision Procedure Config");     
            setupDecisionProcedureGroup(decisionProcGroup, decisionProcedureOption);
            options.add(decisionProcedureOption);
            
            final JRadioButtonMenuItem completeEx = 
                new JRadioButtonMenuItem("Require Complete Execution", false);
            completeEx.setToolTipText("Use only completely executed traces for test" +
                        " generation.");
            completeEx.setSelected(UnitTestBuilder.requireCompleteExecution);
            completeEx.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    UnitTestBuilder.requireCompleteExecution = completeEx.isSelected();
                }
            });
            options.add(completeEx);
                        
            final JRadioButtonMenuItem methodSelectionButton = 
                new JRadioButtonMenuItem("Method Selection Dialog", false);
            methodSelectionButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    openDialog = methodSelectionButton.isSelected();
                }
            });
            methodSelectionButton.setToolTipText("<html><pre>"+
                    "If checked, a dialog for selecting"+
                    " method calls that the created test shall cover" +
                    "\nopens after "+
                    "termination of the symbolic execution.</pre>");
            options.add(methodSelectionButton);
            
            return options;
        }
        
        private void setupDecisionProcedureGroup(ButtonGroup decisionProcGroup, 
                JMenu decisionProcedureOption) {
            final JRadioButtonMenuItem simplifyButton = 
                new JRadioButtonMenuItem("Simplify", ProofSettings.DEFAULT_SETTINGS.
                        getDecisionProcedureSettings().useSimplifyForTest());
            decisionProcGroup.add(simplifyButton);
            decisionProcedureOption.add(simplifyButton);
            
            simplifyButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    ModelGenerator.decProdForTestGen = ModelGenerator.SIMPLIFY;
                    ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().
                    setDecisionProcedureForTest(DecisionProcedureSettings.SIMPLIFY);    
                }
            });
            
            final JRadioButtonMenuItem cogentButton = 
                new JRadioButtonMenuItem("Cogent", 
                        ProofSettings.DEFAULT_SETTINGS.
                        getDecisionProcedureSettings().useCogentForTest());
            decisionProcGroup.add(cogentButton);
            decisionProcedureOption.add(cogentButton);
            
            cogentButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    ModelGenerator.decProdForTestGen = ModelGenerator.COGENT;
                    ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().
                    setDecisionProcedureForTest(DecisionProcedureSettings.COGENT);  
                }
            });

            // In case no decision procedure settings exist yet (for instance if
            // the .key directory was deleted):
            if(!ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().
                    useSimplifyForTest() &&
                    !ProofSettings.DEFAULT_SETTINGS.
                        getDecisionProcedureSettings().useCogentForTest()){
                simplifyButton.setSelected(
                        ModelGenerator.decProdForTestGen == ModelGenerator.SIMPLIFY);
                cogentButton.setSelected(
                        ModelGenerator.decProdForTestGen == ModelGenerator.COGENT);
            }
            // MethodSelectionDialog can change dec. proc. settings. Therefore
            // this is necessary:
            decisionProcedureOption.addMenuListener(new MenuListener(){
                public void menuCanceled(MenuEvent arg0) {}

                public void menuDeselected(MenuEvent arg0) {}

                public void menuSelected(MenuEvent arg0) {
                    simplifyButton.setSelected(
                            ModelGenerator.decProdForTestGen == ModelGenerator.SIMPLIFY);
                    cogentButton.setSelected(
                            ModelGenerator.decProdForTestGen == ModelGenerator.COGENT);
                }
            });
        }    
        
       
        private final class AutoModeAction extends AbstractAction {
            
            private boolean buttonPressed = false;
            private boolean creatingTests = false;
            
            final Icon startLogo = 
                IconFactory.autoModeStartLogo ( toolbarIconSize );
            final Icon stopLogo = 
                IconFactory.autoModeStopLogo ( toolbarIconSize );
                
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
                
                public void proofGoalsAdded(ProofTreeEvent e) { }
            };
                
            public void enable() {
                setEnabled(associatedProof != null && !associatedProof.closed() &&
                        !creatingTests);            
            }
            public AutoModeAction() {
                putValue("hideActionText", Boolean.TRUE);
                putValue(Action.SHORT_DESCRIPTION, AUTO_MODE_TEXT);
                putValue(Action.SMALL_ICON, startLogo);
                
                associatedProof = mediator.getProof();        
                
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
                        autoMode = true;
                        if (associatedProof != null) {
                            associatedProof.removeProofTreeListener(ptl);                        
                        }
                        putValue(Action.SMALL_ICON, stopLogo);
                    }
                    
                    /**
                     * invoked if automatic execution has stopped
                     */
                    public void autoModeStopped(ProofEvent e) {
                        autoMode = false;
                        if(associatedProof!=null){
                            run.setToolTipText("<html><pre>Create Test for:\n"+associatedProof.name()+
                                    "</pre>");
                        }
                        if (associatedProof != null && 
                                associatedProof == e.getSource() && 
                                !associatedProof.containsProofTreeListener(ptl) ) {
                            associatedProof.addProofTreeListener(ptl);
                        }
                        if (associatedProof != null && 
                                buttonPressed &&
                                associatedProof == e.getSource() &&
                                associatedProof.countNodes()>1){ 
                            creatingTests = true;
                            new Thread(new Runnable() {
                                public void run() {
                                    try{
                                        setEnabled(false);
                                        main.setStatusLine("Generating Tests");
                                        StringBuffer testPath = new StringBuffer();
                                        String modelDir = associatedProof.getJavaModel().getModelDir();
                                        test2model.put(testPath, modelDir);
                                        buttonPressed = false;
                                        if(openDialog){
                                            MethodSelectionDialog msd = MethodSelectionDialog.getInstance(mediator);
                                            msd.setLatestTests(testPath);
                                        }else{
                                            UnitTestBuilder testBuilder = 
                                                new UnitTestBuilder(mediator.getServices(), 
                                                        mediator.getProof());
                                            testPath.append(testBuilder.createTestForProof(
                                                    associatedProof)+" ");
                                            
                                            main.setStatusLine("Test Generation Completed");
                                            mediator.testCaseConfirmation(testPath.toString());
                                        }
                                        main.setStatusLine("Test Generation Completed");
                                    }catch(Exception exc){
                                        ExtList l = new ExtList();
                                        l.add(exc);
                                        new ExceptionDialog(testGui, l);
                                    }
                                    creatingTests = false;
                                    enable();
                                }
                            }).start();
                        }
                        putValue(Action.SMALL_ICON, startLogo);     
                    }
                    
                });
                
            }
            
            public void actionPerformed(ActionEvent e) {
                // Unfortunately, when clicking the button twice
                // (very fast), the glasspane won't be quick
                // enough to catch the second event. Therefore
                // we make a second check (which is a %%%HACK)
                if (!autoMode){
     //               setEnabled(false);
                    buttonPressed = true;
                    mediator.startAutoMode();
                }else{
                    mediator.stopAutoMode();
                }
            }
            
        }
    }

   
}
