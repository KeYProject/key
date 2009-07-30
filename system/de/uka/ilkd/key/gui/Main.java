// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.net.URL;
import java.util.Iterator;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.*;
import javax.swing.text.JTextComponent;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.DecisionProcedureSettings.RuleDescriptor;
import de.uka.ilkd.key.gui.configuration.*;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.ExitKeYEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.smt.DecProcRunner;
import de.uka.ilkd.key.strategy.VBTStrategy;
import de.uka.ilkd.key.util.*;
import de.uka.ilkd.key.util.ProgressMonitor;


public class Main extends JFrame implements IMain {

    public static final String INTERNAL_VERSION = 
	KeYResourceManager.getManager().getSHA1();

    private static final String VERSION = 
	KeYResourceManager.getManager().getVersion() + 
	" (internal: "+INTERNAL_VERSION+")";

    private static final String COPYRIGHT="(C) Copyright 2001-2009 "
        +"Universit\u00e4t Karlsruhe, Universit\u00e4t Koblenz-Landau, "
        +"and Chalmers University of Technology";
    
    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;
    
    /** size of the tool bar icons */
    private static final int TOOLBAR_ICON_SIZE = 15;
    
    /** Name of the config file controlling logging with log4j */
    private static final String LOGGER_CONFIGURATION = PathConfig.KEY_CONFIG_DIR + File.separator + "logger.props";
    
    static {
        // @xxx preliminary: better store along with other settings.
        NotationInfo.PRETTY_SYNTAX = true;
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
    
    /** action for opening the PO browser */
    public static POBrowserAction poBrowserAction;
    

    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";

    /** if true then automatically start startAutoMode after the key-file is loaded*/
    public static boolean batchMode = false;
    
    /** A push-button test generation view of KeY*/
    public static boolean testStandalone = false;
    
    /** Determines if the KeY prover is started in visible mode*/
    public static boolean visible = true;

    public static String statisticsFile = null;

    
    
    /** undo the last proof step on the currently selected branch */
    private UndoLastStep undoAction = new UndoLastStep();

    /** external prover GUI elements */
    private DPSettingsListener dpSettingsListener;
    private JSlider ruletimeout;
    private JLabel ruletimeoutlabel;
    private JButton decisionProcedureInvocationButton;

    
    protected static String fileNameOnStartUp = null;
    
    /** are we in stand-alone mode? (or with TCC?) */
    public static boolean standalone = System.getProperty("key.together") == null;
    
    /** for locking of threads waiting for the prover to exit */
    public Object monitor = new Object();
    
    private static final String TACLET_OPTIONS_MENU_STRING = "ToolTip options ";
    
    protected static Main instance = null;    
    
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
        proofListener = new MainProofListener();
        guiListener = new MainGUIListener();
        constraintListener = new MainConstraintTableListener();
        
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
        setSize(1000, 750);
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
            instance = new Main("KeYHeap");
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
    
    
    public static void setStandalone(boolean b) {
        standalone = b;
    }
    
    
    public static void configureLogger() {
        if ((new File(LOGGER_CONFIGURATION)).exists())
            org.apache.log4j.PropertyConfigurator.configureAndWatch(LOGGER_CONFIGURATION, 1500);
        else {
            org.apache.log4j.BasicConfigurator.configure();
            Logger.getRootLogger().setLevel(org.apache.log4j.Level.ERROR);            
        }
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
        
        autoModeAction = new AutoModeAction();
        openFileAction = new OpenFile();
        saveFileAction = new SaveFile();
        poBrowserAction = new POBrowserAction();

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
        toolBar.add(createDecisionProcedureButton());
        toolBar.addSeparator();
        
        final JButton goalBackButton = new JButton();
        undoAction.init();
        goalBackButton.setAction(undoAction);
        
        toolBar.add(goalBackButton);
        toolBar.addSeparator();
                       
        JToolBar fileOperations = new JToolBar("File Operations");
        fileOperations.add(createOpenFile());
        fileOperations.add(createOpenMostRecentFile());
        fileOperations.add(createSaveFile());
        fileOperations.addSeparator();
        fileOperations.add(createPOBrowserComponent());
        
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
                + " See About | License.", getFont());
        getContentPane().add(statusLine, BorderLayout.SOUTH);
    }
    

    private JButton createDecisionProcedureButton() {	
	decisionProcedureInvocationButton = new JButton();	
	RuleDescriptor r = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getActiveRule();
	decisionProcedureInvocationButton.setAction(new DPInvokeAction(r));
	return decisionProcedureInvocationButton;
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

    private JComponent createPOBrowserComponent() {
        final JButton button = new JButton();
        button.setAction(poBrowserAction);
        button.setText("Proof Obligations");
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

            if (standalone) {
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
                ClassTree classTree = new ClassTree(false, false, null, null, currentProof.getServices());
                classTree.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
                scrollpane.setViewportView(classTree);
                pane.add(scrollpane, BorderLayout.CENTER);
            }
            {
                JButton button = new JButton("OK");
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
                }
            }
            dialog.setSize(300, 400);
            dialog.setLocationRelativeTo(this);
            dialog.setVisible(true);
        }
    }

    public void showPOBrowser(){
	if(mediator.getProof() == null){
	    mediator.notify
	    (new GeneralFailureEvent("Please load a proof first"));
	}else{
	    POBrowser poBrowser 
	    	= POBrowser.showInstance(mediator.getProof().env().getInitConfig());
	    ProofOblInput po = poBrowser.getAndClearPO();
	    if(po != null) {
		ProblemInitializer pi = new ProblemInitializer(this);
		try {
		    pi.startProver(mediator.getProof().env(), po);
		} catch(ProofInputException e)  {
		    new ExceptionDialog(this, e);
		}
	    }
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
        pretty.setAccelerator(KeyStroke.getKeyStroke
                            (KeyEvent.VK_P, ActionEvent.CTRL_MASK));        
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
                new UsedSpecificationsDialog(
                             mediator.getServices(), 
                             mediator.getSelectedProof()
                                     .getBasicTask()
                                     .getUsedSpecs());
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
                final Iterator<Node> it = node.childrenIterator();
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
        
        final JMenuItem typeHierInfo = new JMenuItem("Show Known Types");
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
	JMenuItem choiceItem = new JMenuItem("Default Taclet Options...");
	choiceItem.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_T, ActionEvent.CTRL_MASK));

	choiceItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    selectChoices();
		}});
	registerAtMenu(options, choiceItem);	
    
        // decision procedures
        registerAtMenu(options, createDecisionProcedureMenu());
	dpSettingsListener = 
	    new DPSettingsListener(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings());
               
        // specification languages
        JMenuItem speclangItem = setupSpeclangMenu();
        registerAtMenu(options, speclangItem);
        
        addSeparator(options);
        
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
        
	// dnd direction sensitive		
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
        }});
        registerAtMenu(options, oneStepSimplificationOption);
        
        return options;
    }

    /**
     * creates a menu allowing to choose the external prover to be used
     * @return the menu with a list of all available provers that can be used
     */
    private JMenu createDecisionProcedureMenu() {
	/** menu for configuration of decision procedure */
        final JMenu decisionProcedureOption = new JMenu("Decision Procedures");
        
        // the button group which takes care of selecting and unselecting not 
        // activated entries
        final ButtonGroup dpButtonGroup = new ButtonGroup();

	final DecisionProcedureSettings dps = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings();
	for (RuleDescriptor r : dps.getAvailableRules()) {
	    final JRadioButtonMenuItem b = new JRadioButtonMenuItem();
	    b.setAction(new DPSelectionAction(r, b));
	    decisionProcedureOption.add(b);
	    dpButtonGroup.add(b);
	}
		
	decisionProcedureOption.add(new JSeparator());
	
	ruletimeoutlabel = new JLabel();	
	ruletimeoutlabel.setText("timeout: " + dps.getTimeout() + " s");

	decisionProcedureOption.add(ruletimeoutlabel);

	
	ruletimeout = new JSlider(1, 5*60);				
	ruletimeout.setValue(dps.getTimeout());	
	ruletimeout.addChangeListener(new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
		final int newTimeout =((JSlider) e.getSource()).getValue();
		
		ProofSettings ps = ProofSettings.DEFAULT_SETTINGS;
		if (mediator().getProof() != null) {
		    ps = mediator.getProof().getSettings();
		}
		ps.getDecisionProcedureSettings().setTimeout(newTimeout);
	    }	    
	});
	
	// add ruletimeout slider to menu
	decisionProcedureOption.add(ruletimeout);
	
	return decisionProcedureOption;
    }    
    
    
    private JMenuItem setupSpeclangMenu() {
        JMenu result = new JMenu("Specification Languages");       
        ButtonGroup group = new ButtonGroup();
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        
        JRadioButtonMenuItem noneButton 
            = new JRadioButtonMenuItem("None", !gs.useJML() && !gs.useOCL());
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
        
        JRadioButtonMenuItem jmlButton 
            = new JRadioButtonMenuItem("JML", gs.useJML());
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
        ProofSaver saver = new ProofSaver(this, filename);
        String errorMsg = saver.save();
        
        if (errorMsg != null) {
            notify(new GeneralFailureEvent
                    ("Saving Proof failed.\n Error: " + errorMsg));
        }
    }
    
    protected void loadProblem(File file) {
	recentFiles.addRecentFile(file.getAbsolutePath());
        final ProblemLoader pl = 
            new ProblemLoader(file, this, false);
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
    
    private final class DPSettingsListener implements SettingsListener {	
	private DecisionProcedureSettings settings;

	public DPSettingsListener(DecisionProcedureSettings dps) {
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
		RuleDescriptor activeRule = settings.getActiveRule();				
		decisionProcedureInvocationButton.
				
		setAction(new DPInvokeAction(activeRule));
		
		ruletimeoutlabel.setText("timeout: " + settings.getTimeout() + " s");

	    } else {
		assert false;
	    }
	}

	public void settingsChanged(GUIEvent e) {
	    if (e.getSource() instanceof DecisionProcedureSettings) {
		if (e.getSource() != settings) {
		    unregister();
		    settings = (DecisionProcedureSettings) e.getSource();		    
		    register();
		}
		update();
	    }
	}
    }

    /**
     * Loads the last opened file
     */
    private final class OpenMostRecentFile extends AbstractAction {
        
        public OpenMostRecentFile() {
            putValue(SMALL_ICON, IconFactory.openMostRecent(TOOLBAR_ICON_SIZE));
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
            putValue(SMALL_ICON, IconFactory.openKeYFile(TOOLBAR_ICON_SIZE));
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
            putValue(SMALL_ICON, IconFactory.saveFile(TOOLBAR_ICON_SIZE));
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
     * Shows the proof obligation browser.
     */
    private final class POBrowserAction extends AbstractAction {
        
        public POBrowserAction() {
            putValue(NAME, "PO Browser");
            //putValue(SMALL_ICON, IconFactory.saveFile(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Proof Obligation Browser.");
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_B, ActionEvent.CTRL_MASK));
            
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
            showPOBrowser();
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
    
    class MainProofListener implements AutoModeListener, KeYSelectionListener,
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
            dpSettingsListener.settingsChanged(new GUIEvent((proof != null ? 
        	    proof.getSettings() : ProofSettings.DEFAULT_SETTINGS).getDecisionProcedureSettings()));
            makePrettyView();
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
            
            String fileName = Main.fileNameOnStartUp;
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
                System.exit ( 2 ); 
            }
            System.exit ( 0 ); 
        } else {
            // Says that there is at least one open Proof
            System.exit ( 1 );
        }
    }


    
    class MainConstraintTableListener implements ConstraintTableListener {
        public void constraintChanged(ConstraintTableEvent e) {
            setProofNodeDisplay();
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
            sl.reset();
            if (info.getSource() instanceof ApplyStrategy) {
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
                    mediator.getNotationInfo().refresh(mediator.getServices());
                }
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
		} else if (opt[index].equals("AUTO")) {
		    batchMode = true;
                    visible = false;
		} else if (opt[index].equals("DEPTHFIRST")) {		
		    	System.out.println("DepthFirst GoalChooser ...");
			Profile p = ProofSettings.DEFAULT_SETTINGS.getProfile();
			p.setSelectedGoalChooserBuilder(DepthFirstGoalChooserBuilder.NAME);  
			VBTStrategy.preferedGoalChooser = DepthFirstGoalChooserBuilder.NAME;
            
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
	System.out.println("  depthfirst      : constructs the proof tree in a depth first manner. Recommended for large proofs");
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

        public UndoLastStep() {            
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
            putValue(NAME, "Goal Back");
            putValue(SMALL_ICON, 
                    IconFactory.goalBackLogo(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, "Undo the last rule application.");
        }

        private void pruneMode() {
            putValue(NAME, "Prune Proof");
            putValue(SMALL_ICON, IconFactory.goalBackLogo(TOOLBAR_ICON_SIZE));
            putValue(SHORT_DESCRIPTION, 
                    "Prune the tree below the selected node.");
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
    
    
    /**
     * This action is responsible for the invocation of a decision procedure.
     * For example the toolbar button is paramtrized with an instance of this action
     */
    private final class DPInvokeAction extends AbstractAction {

	private final RuleDescriptor decisionProcedure;
	
	public DPInvokeAction(RuleDescriptor decisionProcedure) {
	    assert decisionProcedure != null;
	    this.decisionProcedure = decisionProcedure;

	    putValue(SMALL_ICON, IconFactory.simplifyLogo(TOOLBAR_ICON_SIZE));	    
	  
	    putValue(NAME, decisionProcedure.getDisplayName());
		
	    if (!DecisionProcedureSettings.NOT_A_RULE.equals(decisionProcedure)) {
		putValue(SHORT_DESCRIPTION, "Invoke " + decisionProcedure.getDisplayName());
	    } else {		
		putValue(SHORT_DESCRIPTION, "Please select an external prover under Options | Decision Procedures.");
	    }
	    
	}
	
	public boolean isEnabled() {
	    return super.isEnabled() && !decisionProcedure.equals(DecisionProcedureSettings.NOT_A_RULE) && 
 	      mediator != null && mediator.getProof() != null && !mediator.getProof().closed();
	}
	  
	public void actionPerformed(ActionEvent e) {
	    if (!mediator.ensureProofLoaded()) return;
	    final Proof proof = mediator.getProof();
	    new DecProcRunner(Main.this, proof, 
			proof.getUserConstraint().getConstraint()).run();
	}	
    }
    
    /**
     * This action controls the selection of external provers. It provides the properties for the buttons 
     * displayed in the radio button group and if an external prover is selected this action is invoked and
     * updates the decision procedure settings of the current proof settings. 
     */
    private final class DPSelectionAction extends AbstractAction {
	private final RuleDescriptor decisionProcedure;
	// currently necessary as property SELECTED_KEY support first since JDK >= 1.6
	private final JRadioButtonMenuItem radioButton;
	

	public DPSelectionAction(RuleDescriptor decisionProcedure, JRadioButtonMenuItem radioButton) {	    
	    this.decisionProcedure = decisionProcedure;
	    this.radioButton = radioButton;
	   	  
	    final RuleDescriptor activeRule = getCurrentDPSettings().getActiveRule();
	    
	    if (activeRule.equals(decisionProcedure)) {
		radioButton.setSelected(true);
	    }

	    putValue(SMALL_ICON, IconFactory.simplifyLogo(TOOLBAR_ICON_SIZE));	    

	    putValue(NAME, decisionProcedure.getDisplayName());
	    if (!decisionProcedure.equals(DecisionProcedureSettings.NOT_A_RULE)) {		
		putValue(SHORT_DESCRIPTION, "Use '" + decisionProcedure.getDisplayName() + "' as external prover.");
	    } else {
		putValue(SHORT_DESCRIPTION, "Do not use any external prover.");
	    }

	}
	
	public boolean isEnabled() {
	    return super.isEnabled();
	}
	
	public void actionPerformed(ActionEvent e) {
	    getCurrentDPSettings().setActiveRule(decisionProcedure.getRuleName());
	    radioButton.setSelected(true); // if we change to Java 6 delete radioButton and add here putValue(SELECTED_KEY, true)

	}

	private DecisionProcedureSettings getCurrentDPSettings() {
	    DecisionProcedureSettings dpSettings;
	    if (mediator.getProof() != null) {
		dpSettings = mediator.getProof().getSettings().getDecisionProcedureSettings();
	    } else {
		dpSettings = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings();
	    }
	    return dpSettings;
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
 	
        configureLogger();
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
}
