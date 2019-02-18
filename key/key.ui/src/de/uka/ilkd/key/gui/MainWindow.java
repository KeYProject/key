// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.actions.*;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.ext.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.nodeviews.*;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.ExitKeYEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.proofdiff.ProofDiffFrame;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.smt.ComplexButton;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.settings.SettingsListener;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.util.*;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.util.List;
import java.util.*;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

public final class MainWindow extends JFrame {

    private static final long serialVersionUID = 5853419918923902636L;

    private static MainWindow instance = null;

    /**
     * Search bar for Sequent Views.
     */
    public final SequentViewSearchBar sequentViewSearchBar;

    /**
     * size of the tool bar icons
     */
    public static final int TOOLBAR_ICON_SIZE = 16;

    /**
     * the tab bar at the left
     */
    private final MainWindowTabbedPane mainWindowTabbedPane;

    /**
     * the first toolbar
     */
    private JToolBar controlToolBar;

    /**
     * the second toolbar
     */
    private JToolBar fileOpToolBar;

    /**
     * JScrollPane for displaying SequentViews
     */
    private final MainFrame mainFrame;

    /**
     * the view to show source code and symbolic execution information
     */
    private final JComponent sourceView;

    /**
     * SequentView for the current goal
     */
    public final CurrentGoalView currentGoalView;

    /**
     * Use this SequentView in case no proof is loaded.
     */
    private final EmptySequent emptySequent;

    /**
     * contains a list of all proofs
     */
    private final JScrollPane proofListView;

    private final TaskTree proofList;

    /**
     * the mediator is stored here
     */
    private final KeYMediator mediator;

    /**
     * the user interface which direct all notifications to this window
     */
    private final WindowUserInterfaceControl userInterface;

    /**
     * the status line
     */
    private MainStatusLine statusLine;

    /**
     * listener to global proof events
     */
    private final MainProofListener proofListener;

    private final RecentFileMenu recentFileMenu;

    public boolean frozen = false;

    private static final String PARA =
            "<p style=\"font-family: lucida;font-size: 12pt;font-weight: bold\">";

    /**
     * action for starting and stopping automatic mode
     */
    private final AutoModeAction autoModeAction;

    /**
     * action for opening a KeY file
     */
    private OpenFileAction openFileAction;

    /**
     * action for opening an example
     */
    private OpenExampleAction openExampleAction;

    /**
     * action for opening the most recent KeY file
     */
    private OpenMostRecentFileAction openMostRecentFileAction;

    /**
     * action for editing the most recent KeY file
     */
    private EditMostRecentFileAction editMostRecentFileAction;

    /**
     * action for saving a proof (attempt)
     */
    private SaveFileAction saveFileAction;

    private QuickSaveAction quickSaveAction;
    private QuickLoadAction quickLoadAction;

    /**
     * action for opening the proof management dialog
     */
    private ProofManagementAction proofManagementAction;

    /**
     * action for loading taclets onto a ongoing proof
     */
    private LemmaGenerationAction loadUserDefinedTacletsAction;
    private LemmaGenerationAction loadUserDefinedTacletsForProvingAction;
    private LemmaGenerationAction loadKeYTaclets;
    private LemmaGenerationBatchModeAction lemmaGenerationBatchModeAction;

    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";

    private final NotificationManager notificationManager;

    private final PreferenceSaver prefSaver =
            new PreferenceSaver(Preferences.userNodeForPackage(MainWindow.class));

    private ComplexButton smtComponent;

    /**
     * The menu for the SMT solver options
     */
    public final JMenu smtOptions = new JMenu("SMT Solvers...");

    private ExitMainAction exitMainAction;
    private ShowActiveSettingsAction showActiveSettingsAction;
    private UnicodeToggleAction unicodeToggleAction;
    private final HidePackagePrefixToggleAction hidePackagePrefixToggleAction =
            new HidePackagePrefixToggleAction(this);

    private final TermLabelMenu termLabelMenu;

    public TermLabelVisibilityManager getVisibleTermLabels() {
        return termLabelMenu.getVisibleTermLabels();
    }

    /*
     * This class should only be instantiated once!
     */
    private MainWindow() {
        setTitle(KeYResourceManager.getManager().getUserInterfaceTitle());
        applyGnomeWorkaround();
        setLaF();
        setIconImage(IconFactory.keyLogo());
        setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        proofListener = new MainProofListener();
        userInterface = new WindowUserInterfaceControl(this);
        mediator = getMainWindowMediator(userInterface);
        currentGoalView = new CurrentGoalView(this);
        emptySequent = new EmptySequent(this);
        sequentViewSearchBar = new SequentViewSearchBar(emptySequent);
        termLabelMenu = new TermLabelMenu(this);
        proofListView = new JScrollPane();
        autoModeAction = new AutoModeAction(this);
        mainWindowTabbedPane = new MainWindowTabbedPane(this, mediator, autoModeAction);
        mainFrame = new MainFrame(this, emptySequent);
        sourceView = SourceView.getSourceView(this);
        proofList = new TaskTree(mediator);
        notificationManager = new NotificationManager(mediator, this);
        recentFileMenu = new RecentFileMenu(mediator);
        layoutMain();
        SwingUtilities.updateComponentTreeUI(this);
        ToolTipManager.sharedInstance().setDismissDelay(30000);
        addWindowListener(exitMainAction.windowListener);
        MacroKeyBinding.registerMacroKeyBindings(mediator, currentGoalView, getRootPane());
    }

    public static MainWindow getInstance() {
        return getInstance(true);
    }

    public static MainWindow getInstance(boolean ensureIsVisible) {
        if (GraphicsEnvironment.isHeadless()) {
            System.err.println("Error: KeY started in graphical mode, but no graphical environment present.");
            System.err.println("Please use the --auto option to start KeY in batch mode.");
            System.err.println("Use the --help option for more command line options.");
            System.exit(-1);
        }
        if (instance == null) {
            instance = new MainWindow();
            if (ensureIsVisible) {
                instance.setVisible(true);
            }
        }
        return instance;
    }

    /**
     * <p>
     * Checks if an instance of the main window is already created or not.
     * </p>
     * <p>
     * <b>This method is required, because the Eclipse integration of KeY has
     * to do some cleanup only if a {@link MainWindow} instance exists.</b>
     * </p>
     *
     * @return {@code true} {@link MainWindow} exists and is available via {@link #getInstance()}, {@code false} {@link MainWindow} is not instantiated and will be instantiated via {@link #getInstance()}.
     */
    public static boolean hasInstance() {
        return instance != null;
    }

    /**
     * Workaround to an issue with the Gnome window manager.
     * This sets the application title in the app menu (in the top bar)
     * to "KeY" instead of the full class name ("de-uka-ilkd....").
     * This should not have a negative effect on other window managers.
     * See <a href="http://elliotth.blogspot.de/2007/02/fixing-wmclass-for-your-java.html">
     * here</a> for details.
     */
    private void applyGnomeWorkaround() {
        Toolkit xToolkit = Toolkit.getDefaultToolkit();
        java.lang.reflect.Field awtAppClassNameField;
        try {
            awtAppClassNameField = xToolkit.getClass().getDeclaredField("awtAppClassName");
            awtAppClassNameField.setAccessible(true);
            awtAppClassNameField.set(xToolkit, "KeY");
        } catch (Exception e) {
        }
    }

    /**
     * Tries to set the system look and feel if this option is activated.
     */
    private void setLaF() {
        try {
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().useSystemLaF()) {
                UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());

                // Workarounds for GTK+
                // TODO: check whether they apply to other LaFs
                UIManager.put("Slider.paintValue", Boolean.FALSE);
                UIManager.put("Menu.background", Color.GRAY); // menu background is still white....

                SwingUtilities.updateComponentTreeUI(this);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * Returns the MainWindow KeyMediator.
     *
     * @param userInterface The UserInterfaceControl.
     */
    private KeYMediator getMainWindowMediator(AbstractMediatorUserInterfaceControl userInterface) {
        KeYMediator result = new KeYMediator(userInterface);
        result.addKeYSelectionListener(proofListener);
        // This method delegates the request only to the UserInterfaceControl which implements the functionality.
        // No functionality is allowed in this method body!
        result.getUI().getProofControl().addAutoModeListener(proofListener);
        result.addGUIListener(new MainGUIListener());
        return result;
    }

    /**
     * return the mediator
     *
     * @return the mediator
     */
    public KeYMediator getMediator() {
        if (mediator == null) {
            throw new NullPointerException("KeYMediator is not set.");
        }
        return mediator;
    }

    /**
     * initialised, creates GUI and lays out the main frame
     */
    private void layoutMain() {
        // set overall layout manager
        getContentPane().setLayout(new BorderLayout());

        // default size
        setPreferredSize(new Dimension(1000, 750));

        // FIXME do this NOT in layout of GUI
        // minimize interaction
        final boolean stupidMode =
                ProofIndependentSettings.DEFAULT_INSTANCE
                        .getGeneralSettings().tacletFilter();
        userInterface.getProofControl().setMinimizeInteraction(stupidMode);

        // set up actions
        openFileAction = new OpenFileAction(this);
        openExampleAction = new OpenExampleAction(this);
        openMostRecentFileAction = new OpenMostRecentFileAction(this);
        editMostRecentFileAction = new EditMostRecentFileAction(this);
        saveFileAction = new SaveFileAction(this);
        quickSaveAction = new QuickSaveAction(this);
        quickLoadAction = new QuickLoadAction(this);
        proofManagementAction = new ProofManagementAction(this);
        exitMainAction = new ExitMainAction(this);
        showActiveSettingsAction = new ShowActiveSettingsAction(this);
        loadUserDefinedTacletsAction = new LemmaGenerationAction.ProveAndAddTaclets(this);
        loadUserDefinedTacletsForProvingAction =
                new LemmaGenerationAction.ProveUserDefinedTaclets(this);
        loadKeYTaclets = new LemmaGenerationAction.ProveKeYTaclets(this);
        lemmaGenerationBatchModeAction = new LemmaGenerationBatchModeAction(this);
        unicodeToggleAction = new UnicodeToggleAction(this);

        Config.DEFAULT.setDefaultFonts();

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

        KeYGuiExtensionFacade.createToolbars(this).forEach(toolBarPanel::add);

        getContentPane().add(toolBarPanel, BorderLayout.PAGE_START);

        proofListView.setPreferredSize(new java.awt.Dimension(350, 100));
        GuiUtilities.paintEmptyViewComponent(proofListView, "Proofs");

        JSplitPane leftPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, proofListView, mainWindowTabbedPane);
        leftPane.setName("leftPane");
        leftPane.setOneTouchExpandable(true);

        JPanel rightPane = new JPanel();
        rightPane.setLayout(new BorderLayout());
        rightPane.add(mainFrame, BorderLayout.CENTER);
        rightPane.add(sequentViewSearchBar, BorderLayout.SOUTH);

        JSplitPane pane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, rightPane, sourceView);
        pane.setResizeWeight(0.5);
        pane.setOneTouchExpandable(true);
        pane.setName("split2");

        JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftPane, pane);
        splitPane.setResizeWeight(0); // the right pane is more important
        splitPane.setOneTouchExpandable(true);
        splitPane.setName("splitPane");
        getContentPane().add(splitPane, BorderLayout.CENTER);

        statusLine = new MainStatusLine("<html>" + PARA + KeYConstants.COPYRIGHT + PARA
                + "KeY is free software and comes with ABSOLUTELY NO WARRANTY."
                + " See About | License.", getFont());
        getContentPane().add(statusLine, BorderLayout.SOUTH);

        // load preferred sizes from system preferences
        setName("mainWindow");

        // bugfix: If this is not here, KeY starts with a 0x0 window if invoked
        // for the first time.
        setSize(1000, 600);

        loadPreferences(this);
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
        toolBar.add(new CounterExampleAction(this));
        toolBar.add(new TestGenerationAction(this));
        toolBar.addSeparator();
        toolBar.add(new GoalBackAction(this, false));
        toolBar.add(new PruneProofAction(this));
        toolBar.addSeparator();
        //toolBar.add(createHeatmapToggle());
        //toolBar.add(createHeatmapMenuOpener());

        return toolBar;
    }

    private JToggleButton createHeatmapToggle() {
        return new JToggleButton(new HeatmapToggleAction(this));
    }

    private JButton createHeatmapMenuOpener() {
        return new JButton(new HeatmapSettingsAction(this));
    }

    private ComplexButton createSMTComponent() {
        smtComponent = new ComplexButton(TOOLBAR_ICON_SIZE);
        smtComponent.setEmptyItem("No solver available",
                "<html>No SMT solver is applicable for KeY.<br>" +
                        "<br>If a solver is installed on your system," +
                        "<br>please configure the KeY-System accordingly:\n" +
                        "<br>Options | SMT Solvers</html>");

        smtComponent.setPrefix("Run ");

        smtComponent.addListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                ComplexButton but = (ComplexButton) e.getSource();
                if (but.getSelectedItem() instanceof SMTInvokeAction) {
                    SMTInvokeAction action = (SMTInvokeAction) but.getSelectedItem();
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                            .setActiveSolverUnion(action.solverUnion);
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

    /**
     * @return the status line object
     */
    protected MainStatusLine getStatusLine() {
        return statusLine;
    }

    private void setStandardStatusLineImmediately() {
        statusLine.reset();
    }

    /**
     * Make the status line display a standard message, make progress bar and abort button invisible
     */
    public void setStandardStatusLine() {
        ThreadUtilities.invokeOnEventQueue(new Runnable() {
            @Override
            public void run() {
                setStandardStatusLineImmediately();
            }
        });
    }

    private void setStatusLineImmediately(String str, int max) {
        //statusLine.reset();
        statusLine.setStatusText(str);
        if (max > 0) {
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
        ThreadUtilities.invokeOnEventQueue(new Runnable() {
            @Override
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

    public void selectFirstTab() {
        this.mainWindowTabbedPane.setSelectedIndex(0);
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

    public void makePrettyView() {
        if (getMediator().ensureProofLoaded()) {
            getMediator().getNotationInfo().refresh(mediator.getServices());
            getMediator().getSelectedProof().fireProofGoalsChanged();
        }
    }

    private void addToProofList(de.uka.ilkd.key.proof.ProofAggregate plist) {
        proofList.addProof(plist);
        // GUI
        proofList.setSize(proofList.getPreferredSize());
        proofListView.setViewportView(proofList);
    }

    /**
     * creates menubar entries and adds them to menu bar
     */
    private JMenuBar createMenuBar() {
        JMenuBar menuBar = new JMenuBar();
        menuBar.add(createFileMenu());
        menuBar.add(createViewMenu());
        menuBar.add(createProofMenu());
        menuBar.add(createOptionsMenu());
        createExtensionMenu(menuBar);
        menuBar.add(Box.createHorizontalGlue());
        menuBar.add(createHelpMenu());

        return menuBar;
    }

    private void createExtensionMenu(JMenuBar menuBar) {
        List<KeYMainMenuExtension> menus = KeYGuiExtensionFacade.getMainMenuExtensions();
        if (!menus.isEmpty()) {
            JMenu menu = KeYGuiExtensionFacade.createExtensionMenu(this);
            menuBar.add(menu);
        }
    }

    private JMenu createFileMenu() {
        JMenu fileMenu = new JMenu("File");
        fileMenu.setMnemonic(KeyEvent.VK_F);

        fileMenu.add(openExampleAction);
        fileMenu.add(openFileAction);
        fileMenu.add(openMostRecentFileAction);
        fileMenu.add(editMostRecentFileAction);
        fileMenu.add(saveFileAction);
        fileMenu.add(quickSaveAction);
        fileMenu.add(quickLoadAction);
        fileMenu.addSeparator();
        fileMenu.add(proofManagementAction);


        fileMenu.add(loadUserDefinedTacletsAction);
        JMenu submenu = new JMenu("Prove");
        fileMenu.add(submenu);

        submenu.add(loadUserDefinedTacletsForProvingAction);
        submenu.add(loadKeYTaclets);
        submenu.add(lemmaGenerationBatchModeAction);
        fileMenu.addSeparator();
        fileMenu.add(recentFileMenu.getMenu());
        fileMenu.addSeparator();
        fileMenu.add(exitMainAction);
        return fileMenu;
    }

    private JMenu createViewMenu() {
        JMenu view = new JMenu("View");
        view.setMnemonic(KeyEvent.VK_V);

        JMenuItem laf = new JCheckBoxMenuItem("Use system look and feel (experimental)");
        laf.setToolTipText("If checked KeY tries to appear in the look and feel of your " +
                "window manager, if not in the default Java LaF (aka Metal).");
        final de.uka.ilkd.key.settings.ViewSettings vs =
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        laf.setSelected(vs.useSystemLaF());
        laf.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                vs.setUseSystemLaF(((JCheckBoxMenuItem) e.getSource()).
                        isSelected());
                // TODO: inform that this requires a restart
                System.out.println("Info: Look and feel changed for next start of KeY.");
            }
        });
//        view.add(laf); // uncomment this line to include the option in the menu


        view.add(new JCheckBoxMenuItem(new PrettyPrintToggleAction(this)));
        view.add(new JCheckBoxMenuItem(unicodeToggleAction));
        view.add(new JCheckBoxMenuItem(new SyntaxHighlightingToggleAction(this)));
        view.add(termLabelMenu);
        view.add(new JCheckBoxMenuItem(hidePackagePrefixToggleAction));

        view.addSeparator();
        {
            JMenu fontSize = new JMenu("Font Size");
            fontSize.add(new DecreaseFontSizeAction(this));
            fontSize.add(new IncreaseFontSizeAction(this));
            view.add(fontSize);
        }
        view.add(new ToolTipOptionsAction(this));

        view.add(new ProofDiffFrame.Action(this));

        view.addSeparator();

        JMenuItem hmItem = new JMenuItem("Heatmap Options");
        hmItem.addActionListener(new HeatmapSettingsAction(this));
        view.add(hmItem);

        return view;
    }

    private JMenu createProofMenu() {
        JMenu proof = new JMenu("Proof");
        proof.setMnemonic(KeyEvent.VK_P);

        proof.add(autoModeAction);
        GoalBackAction goalBack = new GoalBackAction(this, true);
        proof.addMenuListener(new MenuListener() {
            @Override
            public void menuSelected(MenuEvent e) {
                /* we use this MenuListener to update the name only if the menu is shown since it
                 * would be slower to update the name (which means scanning all open and closed
                 * goals) at every selection change (via the KeYSelectionListener in GoalBackAction)
                 */
                goalBack.updateName();
            }

            @Override
            public void menuDeselected(MenuEvent e) {
            }

            @Override
            public void menuCanceled(MenuEvent e) {
            }
        });
        proof.add(goalBack);
        proof.add(new PruneProofAction(this));
        proof.add(new AbandonTaskAction(this));
        proof.addSeparator();
        proof.add(new SearchInProofTreeAction(this));
        proof.add(new SearchInSequentAction(this));
        proof.addSeparator();
        proof.add(new ShowUsedContractsAction(this));
        proof.add(new ShowActiveTactletOptionsAction(this));
        proof.add(showActiveSettingsAction);
        proof.add(new ShowProofStatistics(this));
        proof.add(new ShowKnownTypesAction(this));
        proof.addSeparator();
        proof.add(new CounterExampleAction(this));
        proof.add(new TestGenerationAction(this));

        return proof;
    }

    private JMenu createOptionsMenu() {
        JMenu options = new JMenu("Options");
        options.setMnemonic(KeyEvent.VK_O);

        options.add(new TacletOptionsAction(this));
        options.add(new SMTOptionsAction(this));
//	options.add(setupSpeclangMenu()); // legacy since only JML supported
        options.addSeparator();
        options.add(new JCheckBoxMenuItem(new ToggleConfirmExitAction(this)));
        options.add(new JCheckBoxMenuItem(new AutoSave(this)));
        options.add(new MinimizeInteraction(this));
        options.add(new JCheckBoxMenuItem(new RightMouseClickToggleAction(this)));

        return options;

    }

    private JMenu createHelpMenu() {
        JMenu help = new JMenu("About");
        help.setMnemonic(KeyEvent.VK_A);

        help.add(new AboutAction(this));
        help.add(new KeYProjectHomepageAction(this));
//        help.add(new SystemInfoAction(this));
        help.add(new MenuSendFeedackAction(this));
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

        if (solverUnions == null || solverUnions.isEmpty()) {
            updateDPSelectionMenu();
        } else {
            updateDPSelectionMenu(solverUnions);
        }

    }

    private void updateDPSelectionMenu() {
        smtComponent.setItems(null);
    }

    private SMTInvokeAction findAction(SMTInvokeAction[] actions, SolverTypeCollection union) {
        for (SMTInvokeAction action : actions) {
            if (action.solverUnion.equals(union)) {
                return action;
            }
        }
        return null;
    }

    private void updateDPSelectionMenu(Collection<SolverTypeCollection> unions) {
        SMTInvokeAction actions[] = new SMTInvokeAction[unions.size()];

        int i = 0;
        for (SolverTypeCollection union : unions) {

            actions[i] = new SMTInvokeAction(union);
            i++;
        }

        smtComponent.setItems(actions);

        SolverTypeCollection active = ProofIndependentSettings
                .DEFAULT_INSTANCE.getSMTSettings().computeActiveSolverUnion();

        SMTInvokeAction activeAction = findAction(actions, active);

        boolean found = activeAction != null;
        if (!found) {
            Object item = smtComponent.getTopItem();
            if (item instanceof SMTInvokeAction) {
                active = ((SMTInvokeAction) item).solverUnion;
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                        .setActiveSolverUnion(active);
            } else {
                activeAction = null;
            }

        }
        smtComponent.setSelectedItem(activeAction);
    }

    JCheckBoxMenuItem saveSMTFile;

    @SuppressWarnings("unused")
    // currently not used because we only have one specification language
    private JMenuItem setupSpeclangMenu() {
        JMenu result = new JMenu("Specification Parser");
        ButtonGroup group = new ButtonGroup();
        GeneralSettings gs
                = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        JRadioButtonMenuItem jmlButton
                = new JRadioButtonMenuItem("Source File Comments Are JML", gs.useJML());
        result.add(jmlButton);
        group.add(jmlButton);
        jmlButton.setIcon(IconFactory.jmlLogo(15));
        jmlButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
                gs.setUseJML(true);
            }
        });

        JRadioButtonMenuItem noneButton
                = new JRadioButtonMenuItem("Source File Comments Are Ignored", !gs.useJML());
        result.add(noneButton);
        group.add(noneButton);
        noneButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
                gs.setUseJML(false);
            }
        });

        return result;
    }

    public ProofTreeView getProofTreeView() {
        return mainWindowTabbedPane.getProofTreeView();
    }

    /**
     * Returns the current goal view.
     */
    public CurrentGoalView getGoalView() {
        return currentGoalView;
    }

    public void addProblem(final de.uka.ilkd.key.proof.ProofAggregate plist) {
        Runnable guiUpdater = new Runnable() {
            @Override
            public void run() {
                disableCurrentGoalView = true;
                addToProofList(plist);
                setUpNewProof(plist.getFirstProof());
                disableCurrentGoalView = false;
                updateSequentView();
            }
        };
        ThreadUtilities.invokeOnEventQueue(guiUpdater);
    }

    private Proof setUpNewProof(Proof proof) {
        getMediator().setProof(proof);
        return proof;
    }

    /**
     * invoked if a frame that wants modal access is opened
     */
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
            doNotReenable = new LinkedHashSet<Component>();
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
            if (doNotReenable == null) {
                // bug #1105 occurred
                Debug.out("toolbar enabled w/o prior disable");
                return;
            }

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

        @Override
        public void modalDialogOpened(EventObject e) {

            if (e.getSource() instanceof ApplyTacletDialog) {
                // disable all elements except the sequent window (drag'n'drop !) ...
                enableMenuBar(MainWindow.this.getJMenuBar(), false);
                MainWindow.this.mainFrame.setEnabled(false);
                mainWindowTabbedPane.setEnabledForAllTabs(false);
                setToolBarDisabled();
            } else {
                // disable the whole main window ...
                MainWindow.this.setEnabled(false);
            }
        }

        /**
         * invoked if a frame that wants modal access is closed
         */
        @Override
        public void modalDialogClosed(EventObject e) {
            if (e.getSource() instanceof ApplyTacletDialog) {
                // enable all previously disabled elements ...
                enableMenuBar(MainWindow.this.getJMenuBar(), true);
                MainWindow.this.mainFrame.setEnabled(true);
                mainWindowTabbedPane.setEnabledForAllTabs(true);
                setToolBarEnabled();
            } else {
                // enable the whole main window ...
                MainWindow.this.setEnabled(true);
            }
        }

        @Override
        public void shutDown(EventObject e) {
            MainWindow.this.notify(new ExitKeYEvent());
            MainWindow.this.setVisible(false);
        }

    }

    /**
     * set to true if the view of the current goal should not be updated
     */
    private boolean disableCurrentGoalView = false;

    /*
     * Updates the sequent displayed in the main frame.
     */
    private synchronized void updateSequentView() {

        if (disableCurrentGoalView) {
            return;
        }

        final SequentView newSequentView;

        if (getMediator().getSelectedProof() == null) {
            newSequentView = emptySequent;
        } else {
            Goal goal = getMediator().getSelectedGoal();
            if (goal != null && !goal.node().isClosed()) {
                currentGoalView.setPrinter(goal);
                currentGoalView.printSequent();
                newSequentView = currentGoalView;
            } else {
                newSequentView = new InnerNodeView(getMediator().getSelectedNode(), this);
            }
        }

        Runnable sequentUpdater = new Runnable() {
            @Override
            public void run() {
                mainFrame.setContent(newSequentView);
                sequentViewSearchBar.setSequentView(newSequentView);
            }
        };

        if (SwingUtilities.isEventDispatchThread()) {
            sequentUpdater.run();
        } else {
            SwingUtilities.invokeLater(sequentUpdater);
        }

    }

    class MainProofListener implements AutoModeListener, KeYSelectionListener,
            SettingsListener {

        Proof proof = null;

        /**
         * focused node has changed
         */
        @Override
        public synchronized void selectedNodeChanged(KeYSelectionEvent e) {
            if (getMediator().isInAutoMode()) {
                return;
            }
            updateSequentView();
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public synchronized void selectedProofChanged(KeYSelectionEvent e) {
            Debug.out("Main: initialize with new proof");

            if (proof != null && !proof.isDisposed()) {
                proof.getSettings().getStrategySettings().removeSettingsListener(this);
            }
            proof = e.getSource().getSelectedProof();
            if (proof != null) {
                proof.getSettings().getStrategySettings().addSettingsListener(this);
            }

            disableCurrentGoalView = false;
            updateSequentView();
            makePrettyView();
        }

        /**
         * invoked if automatic execution has started
         */
        @Override
        public synchronized void autoModeStarted(ProofEvent e) {
            Debug.log4jWarn("Automode started", MainWindow.class.getName());
            disableCurrentGoalView = true;
            getMediator().removeKeYSelectionListener(proofListener);
            freezeExceptAutoModeButton();
        }

        /**
         * invoked if automatic execution has stopped
         */
        @Override
        public synchronized void autoModeStopped(ProofEvent e) {
            if (Debug.ENABLE_DEBUG) {
                Debug.log4jWarn("Automode stopped", MainWindow.class.getName());
                Debug.log4jDebug("From " + Debug.stackTrace(),
                        MainWindow.class.getName());
            }
            unfreezeExceptAutoModeButton();
            disableCurrentGoalView = false;
            updateSequentView();
            getMediator().addKeYSelectionListener(proofListener);
        }

        /**
         * invoked when the strategy of a proof has been changed
         */
        @Override
        public synchronized void settingsChanged(EventObject e) {
            if (proof.getSettings().getStrategySettings() == e.getSource()) {
                // updateAutoModeConfigButton();
            }
        }
    }

    void displayResults(String message) {
        setStatusLine(message);
    }

    /**
     * Glass pane that only delivers events for the status line (i.e. the abort button)
     * <p>
     * This has been partly taken from the GlassPaneDemo of the Java Tutorial
     */
    private static class BlockingGlassPane extends JComponent {
        /**
         *
         */
        private static final long serialVersionUID = 1218022319090988424L;
        private final GlassPaneListener listener;

        public BlockingGlassPane(Container contentPane) {
            setCursor(new Cursor(Cursor.WAIT_CURSOR));

            listener = new GlassPaneListener(this, contentPane);
            addMouseListener(listener);
            addMouseMotionListener(listener);
            addKeyListener(new KeyListener() {

                @Override
                public void keyPressed(KeyEvent e) {
                    e.consume();
                }

                @Override
                public void keyReleased(KeyEvent e) {
                    e.consume();

                }

                @Override
                public void keyTyped(KeyEvent e) {
                    e.consume();
                }

            });
        }
    }

    /**
     * Mouse listener for the glass pane that only delivers events for the status line (i.e. the
     * abort button)
     * <p>
     * This has been partly taken from the GlassPaneDemo of the Java Tutorial
     */
    private static class GlassPaneListener extends MouseInputAdapter {
        Component currentComponent = null;
        Component glassPane;
        Container contentPane;

        public GlassPaneListener(Component glassPane,
                                 Container contentPane) {
            this.glassPane = glassPane;
            this.contentPane = contentPane;
        }

        @Override
        public void mouseMoved(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        /*
         * We must forward at least the mouse drags that started with mouse presses over the check box.
         * Otherwise, when the user presses the check box then drags off, the check box isn't disarmed --
         * it keeps its dark gray background or whatever its L&F uses to indicate that the button is
         * currently being pressed.
         */
        @Override
        public void mouseDragged(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        @Override
        public void mouseEntered(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        @Override
        public void mouseExited(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        @Override
        public void mousePressed(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        @Override
        public void mouseReleased(MouseEvent e) {
            redispatchMouseEvent(e);
            currentComponent = null;
        }

        private void redispatchMouseEvent(MouseEvent e) {
            if (currentComponent != null) {
                dispatchForCurrentComponent(e);
            } else {
                int eventID = e.getID();
                Point glassPanePoint = e.getPoint();

                Point containerPoint =
                        SwingUtilities.convertPoint(glassPane,
                                glassPanePoint,
                                contentPane);
                Component component =
                        SwingUtilities.getDeepestComponentAt(contentPane,
                                containerPoint.x,
                                containerPoint.y);

                if (eventID == MouseEvent.MOUSE_PRESSED &&
                        isLiveComponent(component)) {
                    currentComponent = component;
                    dispatchForCurrentComponent(e);
                }
            }
        }

        // FIXME This is not really good.
        private boolean isLiveComponent(Component c) {
            // this is not the most elegant way to identify the right
            // components, but it scales well ;-)
            while (c != null) {
                if ((c instanceof JComponent) &&
                        AUTO_MODE_TEXT.equals(((JComponent) c).getToolTipText())) {
                    return true;
                }
                c = c.getParent();
            }
            return false;
        }

        private void dispatchForCurrentComponent(MouseEvent e) {
            Point glassPanePoint = e.getPoint();
            Point componentPoint =
                    SwingUtilities.convertPoint(glassPane,
                            glassPanePoint,
                            currentComponent);
            currentComponent.dispatchEvent(new MouseEvent(currentComponent,
                    e.getID(),
                    e.getWhen(),
                    // do not use as it freezes the stop button: e.getModifiersEx(),
                    e.getModifiers(),
                    componentPoint.x,
                    componentPoint.y,
                    e.getClickCount(),
                    e.isPopupTrigger()));
        }
    }

    private final class DPEnableControl implements KeYSelectionListener {

        private void enable(boolean b) {
            smtComponent.setEnabled(b);
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {

            if (e.getSource().getSelectedProof() != null) {
                enable(!e.getSource().getSelectedProof().closed());
            } else {
                enable(false);
            }

        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            selectedProofChanged(e);

        }

    }


    /**
     * This action is responsible for the invocation of an SMT solver For
     * example the toolbar button is parameterized with an instance of this action
     */
    private final class SMTInvokeAction extends MainWindowAction {
        /**
         *
         */
        private static final long serialVersionUID = -8176122007799747342L;

        SolverTypeCollection solverUnion;

        public SMTInvokeAction(SolverTypeCollection solverUnion) {
            super(MainWindow.this);
            this.solverUnion = solverUnion;
            if (solverUnion != SolverTypeCollection.EMPTY_COLLECTION) {
                putValue(SHORT_DESCRIPTION, "Invokes " + solverUnion.toString());
            }
        }

        @Override
        public boolean isEnabled() {
            boolean b = super.isEnabled() && solverUnion != SolverTypeCollection.EMPTY_COLLECTION
                    && mediator != null
                    && mediator.getSelectedProof() != null
                    && !mediator.getSelectedProof().closed();
            return b;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (!mediator.ensureProofLoaded() || solverUnion == SolverTypeCollection.EMPTY_COLLECTION) {
                MainWindow.this.popupWarning("No proof loaded or no solvers selected.", "Oops...");
                return;
            }
            final Proof proof = mediator.getSelectedProof();

            Thread thread = new Thread(new Runnable() {
                @Override
                public void run() {

                    SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
                            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
                    SolverLauncher launcher = new SolverLauncher(settings);
                    launcher.addListener(new SolverListener(settings, proof));
                    launcher.launch(solverUnion.getTypes(),
                            SMTProblem.createSMTProblems(proof),
                            proof.getServices());

                }
            }, "SMTRunner");
            thread.start();

        }

        @Override
        public String toString() {
            return solverUnion.toString();
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof SMTInvokeAction)) {
                return false;
            }
            return this.solverUnion.equals(((SMTInvokeAction) obj).solverUnion);
        }

        @Override
        public int hashCode() {
            return solverUnion.hashCode() * 7;
        }

    }

    /**
     * informs the NotificationManager about an event
     *
     * @param event the NotificationEvent
     */
    public void notify(NotificationEvent event) {
        if (notificationManager != null) {
            notificationManager.handleNotificationEvent(event);
        }
    }

    public void popupInformationMessage(Object message, String title) {
        JOptionPane.showMessageDialog(this, message, title, JOptionPane.INFORMATION_MESSAGE);
    }

    public void popupWarning(Object message, String title) {
        JOptionPane.showMessageDialog(this, message, title, JOptionPane.WARNING_MESSAGE);
    }

    /**
     * Brings up a dialog displaying a message.
     *
     * @param modal whether or not the message should be displayed in a modal dialog.
     */
    public void popupInformationMessage(Object message, String title, boolean modal) {
        if (modal) {
            popupInformationMessage(message, title);
        } else {
            if (!(message instanceof Component)) {
                throw new InternalError("only messages of type " + Component.class + " supported, yet");
            }
            JFrame dlg = new JFrame(title);
            dlg.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            dlg.getContentPane().add((Component) message);
            dlg.pack();
            GuiUtilities.setCenter(dlg, this);
            dlg.setVisible(true);
        }
    }


    public TaskTree getProofList() {
        return proofList;
    }

    public RecentFileMenu getRecentFiles() {
        return recentFileMenu;
    }

    public WindowUserInterfaceControl getUserInterface() {
        return userInterface;
    }

    public Action getOpenMostRecentFileAction() {
        return openMostRecentFileAction;
    }

    public Action getUnicodeToggleAction() {
        return unicodeToggleAction;
    }

    public Action getHidePackagePrefixToggleAction() {
        return hidePackagePrefixToggleAction;
    }

    /**
     * Store the properties of the named components under {@code component} to
     * the system preferences.
     * <p>
     * This uses the {@link Preferences} class to access the system preferences.
     * Preferences are not explicitly synchronised; this happens at application
     * end using {@link #syncPreferences()}. All components which are in the
     * component tree are queried.
     *
     * @param component the non-null component whose preferences are to be saved
     * @see PreferenceSaver
     */
    public void savePreferences(Component component) {
        prefSaver.save(component);
    }

    /**
     * Load the properties of the named components under {@code component} from
     * the system preferences.
     * <p>
     * This uses the {@link Preferences} class to access the system preferences.
     * All components which are in the component tree are queried.
     *
     * @param component the non-null component whose preferences are to be set
     * @see PreferenceSaver
     */
    public final void loadPreferences(Component component) {
        prefSaver.load(component);
    }

    /**
     * Synchronised the system properties with the background storage system.
     * <p>
     * This is typically called at application termination.
     *
     * @see PreferenceSaver
     */
    public final void syncPreferences() {
        try {
            prefSaver.flush();
        } catch (BackingStoreException e) {
            // it is not tragic if the preferences cannot be stored.
            e.printStackTrace();
        }
    }

    /**
     * <p>
     * Returns the {@link ExitMainAction} that is used to exit the {@link MainWindow}.
     * </p>
     * <p>
     * This functionality is required because for instance other projects
     * like the Eclipse integration has to close the main window.
     * </p>
     *
     * @return The used {@link ExitMainAction}.
     */
    public ExitMainAction getExitMainAction() {
        return exitMainAction;
    }

    /**
     * <p>
     * Returns the {@link NotificationManager}.
     * </p>
     * <p>
     * This functionality is required because in other project is it
     * required to execute the automatic mode without opening the result dialog
     * which can be disabled in the {@link NotificationManager}.
     * </p>
     *
     * @return
     */
    public NotificationManager getNotificationManager() {
        return notificationManager;
    }

    protected void addRecentFile(String absolutePath) {
        recentFileMenu.addRecentFile(absolutePath);
    }

    public void openExamples() {
        openExampleAction.actionPerformed(null);
    }

    public void loadProblem(File file) {
        getUserInterface().loadProblem(file);
    }

    public void loadProblem(File file, List<File> classPath, File bootClassPath, List<File> includes) {
        getUserInterface().loadProblem(file, classPath, bootClassPath, includes);
    }

    /*
     * Retrieves supported term label names from profile and returns a sorted
     * list of them.
     */
    public List<Name> getSortedTermLabelNames() {
        /*
         * Get list of labels from profile. This list is not always identical,
         * since the used Profile may change during execution.
         */
        return TermLabelVisibilityManager.getSortedTermLabelNames(getMediator().getProfile());
    }

    /**
     * Returns the {@link JToolBar} with the proof control.
     * <p>
     * This method is used by the Eclipse world to add additional features!
     *
     * @return The {@link JToolBar} with the proof control.
     */
    public JToolBar getControlToolBar() {
        return controlToolBar;
    }

    /**
     * Defines if talcet infos are shown or not.
     * <p>
     * Used by the Eclipse integration.
     *
     * @param show {@code true} show taclet infos, {@code false} hide taclet infos.
     */
    public void setShowTacletInfo(boolean show) {
        mainWindowTabbedPane.getProofTreeView().tacletInfoToggle.setSelected(show);
    }


    public AutoModeAction getAutoModeAction() {
        return autoModeAction;
    }
}
