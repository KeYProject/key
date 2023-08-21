/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.List;
import java.util.function.Function;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.event.ChangeListener;
import javax.swing.event.MenuEvent;
import javax.swing.event.MenuListener;
import javax.swing.event.MouseInputAdapter;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.actions.*;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.gui.nodeviews.*;
import de.uka.ilkd.key.gui.notification.NotificationManager;
import de.uka.ilkd.key.gui.notification.events.ExitKeYEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.plugins.action_history.ActionHistoryExtension;
import de.uka.ilkd.key.gui.proofdiff.ProofDiffFrame;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.settings.FontSizeFacade;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.smt.DropdownSelectionButton;
import de.uka.ilkd.key.gui.sourceview.SourceViewFrame;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.gui.utilities.LruCached;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.util.*;

import bibliothek.gui.dock.StackDockStation;
import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.SingleCDockable;
import bibliothek.gui.dock.common.intern.CDockable;
import bibliothek.gui.dock.station.stack.tab.layouting.TabPlacement;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@HelpInfo()
public final class MainWindow extends JFrame {

    /**
     * size of the tool bar icons
     */
    public static final int TOOLBAR_ICON_SIZE = 16;
    /**
     * size of the tab icons
     */
    public static final float TAB_ICON_SIZE = 16f;
    /**
     * Tooltip for auto mode button.
     */
    public static final String AUTO_MODE_TEXT = "Start/stop automated proof search";
    private static final long serialVersionUID = 5853419918923902636L;
    private static final String PARA =
        "<p style=\"font-family: lucida;font-size: 12pt;font-weight: bold\">";

    private static final Logger LOGGER = LoggerFactory.getLogger(MainWindow.class);

    private static MainWindow instance = null;
    /**
     * Search bar for Sequent Views.
     */
    private final SequentViewSearchBar sequentViewSearchBar;
    /**
     * SequentView for the current goal
     */
    private final CurrentGoalView currentGoalView;

    private final GoalList openGoalsView;
    private final ProofTreeView proofTreeView;
    private final InfoView infoView;
    private final StrategySelectionView strategySelectionView;
    /**
     * JScrollPane for displaying SequentViews
     */
    private final MainFrame mainFrame;
    /**
     * the view to show source code and symbolic execution information
     */
    private final SourceViewFrame sourceViewFrame;
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
     * listener to global proof events
     */
    private final MainProofListener proofListener;

    private final RecentFileMenu recentFileMenu;
    /**
     * action for starting and stopping automatic mode
     */
    private final AutoModeAction autoModeAction;
    private final NotificationManager notificationManager;
    private final PreferenceSaver prefSaver =
        new PreferenceSaver(Preferences.userNodeForPackage(MainWindow.class));
    private final HidePackagePrefixToggleAction hidePackagePrefixToggleAction =
        new HidePackagePrefixToggleAction(this);
    private final ToggleSequentViewTooltipAction toggleSequentViewTooltipAction =
        new ToggleSequentViewTooltipAction(this);
    private final ToggleSourceViewTooltipAction toggleSourceViewTooltipAction =
        new ToggleSourceViewTooltipAction(this);
    private final TermLabelMenu termLabelMenu;
    private boolean frozen = false;
    /**
     *
     */
    private final CControl dockControl = new CControl(this);
    /**
     * the first toolbar
     */
    private JToolBar controlToolBar;
    /**
     * the second toolbar
     */
    private JToolBar fileOpToolBar;
    /**
     * the status line
     */
    private MainStatusLine statusLine;
    /**
     * action for opening a KeY file
     */
    private OpenFileAction openFileAction;

    private OpenSingleJavaFileAction openSingleJavaFileAction;

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
    /**
     * action for saving a proof as a bundle
     */
    private SaveBundleAction saveBundleAction;
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


    /**
     * actions for changing the selection on the proof tree
     */
    private GoalSelectAboveAction goalSelectAboveAction;
    private GoalSelectBelowAction goalSelectBelowAction;
    private DropdownSelectionButton smtComponent;
    private DropdownSelectionButton.EmptyAction noSolverSelected;
    private ChangeListener selectAllListener;
    private JCheckBoxMenuItem selectAll;
    private JSeparator separator;
    private ExitMainAction exitMainAction;
    private ShowActiveSettingsAction showActiveSettingsAction;
    private UnicodeToggleAction unicodeToggleAction;
    private SelectionBackAction selectionBackAction;
    private SelectionForwardAction selectionForwardAction;

    private SingleCDockable dockProofListView;
    private SingleCDockable dockSourceView;
    private SingleCDockable dockSequent;

    /*
     * A function collapsing multiple SMTInvokeActions into one that starts a union of all solver
     * types contained in any of the input actions. None-SMTInvokeActions in the input are ignored.
     */
    private final Function<Action[], Action> collapseChoice = a -> {
        Set<SolverType> types = new HashSet<>();
        StringBuilder builder = new StringBuilder();
        for (Action action : a) {
            // Ignore all none-SMTInvokeActions
            if (action instanceof SMTInvokeAction) {
                types.addAll(((SMTInvokeAction) action).getSolverUnion().getTypes());
            }
        }
        if (types.isEmpty() || a.length == 0) {
            return noSolverSelected;
        }
        for (SolverType type : types) {
            builder.append(type.getName()).append(", ");
        }
        builder.delete(builder.length() - 2, builder.length());
        SolverTypeCollection chosenSolvers =
            new SolverTypeCollection(builder.toString(), types.size(), types);
        return new SMTInvokeAction(chosenSolvers, this);
    };

    /**
     * set to true if the view of the current goal should not be updated
     */
    private boolean disableCurrentGoalView = false;

    private final LruCached<HTMLSyntaxHighlighter.Args, String> highlightCache =
        new LruCached<>(HTMLSyntaxHighlighter.Args::run);

    /*
     * This class should only be instantiated once!
     */
    private MainWindow() {
        InputMap inputMap =
            getRootPane().getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        inputMap.put(HelpFacade.ACTION_OPEN_HELP.getAcceleratorKey(), HelpFacade.ACTION_OPEN_HELP);
        getRootPane().getActionMap().put(HelpFacade.ACTION_OPEN_HELP, HelpFacade.ACTION_OPEN_HELP);

        setTitle(KeYResourceManager.getManager().getUserInterfaceTitle());
        setLocationByPlatform(true);
        applyGnomeWorkaround();
        if (!applyTaskbarIcon()) {
            applyMacOsWorkaround();
        }
        setLaF();
        setIconImages(IconFactory.applicationLogos());


        setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        proofListener = new MainProofListener();
        userInterface = new WindowUserInterfaceControl(this);
        mediator = getMainWindowMediator(userInterface);
        KeYGuiExtensionFacade.getStartupExtensions().forEach(it -> it.preInit(this, mediator));

        Config.DEFAULT.setDefaultFonts();
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        FontSizeFacade.resizeFonts(vs.getUIFontSizeFactor());

        termLabelMenu = new TermLabelMenu(this);
        currentGoalView = new CurrentGoalView(this);
        emptySequent = new EmptySequent(this);
        sequentViewSearchBar = new SequentViewSearchBar(emptySequent);
        proofListView = new JScrollPane();
        autoModeAction = new AutoModeAction(this);
        mainFrame = new MainFrame(this, emptySequent);
        sourceViewFrame = new SourceViewFrame(this);
        proofList = new TaskTree(mediator);
        notificationManager = new NotificationManager(mediator, this);
        recentFileMenu = new RecentFileMenu(mediator);

        proofTreeView = new ProofTreeView(mediator);
        infoView = new InfoView(this, mediator);
        strategySelectionView = new StrategySelectionView(this, mediator);
        openGoalsView = new GoalList(mediator);

        layoutMain();
        SwingUtilities.updateComponentTreeUI(this);
        ToolTipManager.sharedInstance().setDismissDelay(30000);
        addWindowListener(exitMainAction.windowListener);
        MacroKeyBinding.registerMacroKeyBindings(mediator, currentGoalView, getRootPane());

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, (JComponent) getContentPane(),
            KeYGuiExtension.KeyboardShortcuts.MAIN_WINDOW);

        KeYGuiExtensionFacade.getStartupExtensions().forEach(it -> it.init(this, mediator));

        DockingHelper.focus(this, ProofTreeView.class);
    }

    public LruCached<HTMLSyntaxHighlighter.Args, String> getHighlightCache() {
        return highlightCache;
    }

    /**
     *
     */
    private boolean applyTaskbarIcon() {
        // https://stackoverflow.com/questions/50403677/changing-the-default-java-coffee-dock-icon-to-something-else
        try {
            Image image = IconFactory.keyLogo();
            Class<?> appClass = Class.forName("java.awt.Taskbar");
            Method getTaskbar = appClass.getMethod("getTaskbar");
            Method setIconImage = appClass.getMethod("setIconImage", Image.class);
            Object taskbar = getTaskbar.invoke(null); // static method
            setIconImage.invoke(taskbar, image);
            return true;
        } catch (ClassNotFoundException | NoSuchMethodException | IllegalAccessException
                | InvocationTargetException e) {
            return false;
        }
    }

    /**
     * Set the dock image on MacOS <=10.6.
     */
    private boolean applyMacOsWorkaround() {
        // https://stackoverflow.com/questions/50403677/changing-the-default-java-coffee-dock-icon-to-something-else
        try {
            Class<?> appClass = Class.forName("com.apple.eawt.Application");
            Class<?>[] params = new Class[] { Image.class };
            Method getApplication = appClass.getMethod("getApplication");
            Object application = getApplication.invoke(appClass);
            Method setDockIconImage = appClass.getMethod("setDockIconImage", params);
            setDockIconImage.invoke(application, IconFactory.keyLogo());
            return true;
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException
                | ClassNotFoundException ignored) {
            return false;
        }
    }

    public static MainWindow getInstance() {
        return getInstance(true);
    }

    public static MainWindow getInstance(boolean ensureIsVisible) {
        if (GraphicsEnvironment.isHeadless()) {
            LOGGER.error(
                "Error: KeY started in graphical mode, " + "but no graphical environment present.");
            LOGGER.error("Please use the --auto option to start KeY in batch mode.");
            LOGGER.error("Use the --help option for more command line options.");
            System.exit(-1);
        }
        // always construct MainWindow on event dispatch thread
        if (!EventQueue.isDispatchThread()) {
            try {
                SwingUtilities.invokeAndWait(MainWindow::getInstance);
            } catch (InterruptedException | InvocationTargetException e) {
                throw new RuntimeException(e);
            }
            return instance;
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
     * <b>This method is required, because the Eclipse integration of KeY has to do some cleanup
     * only if a {@link MainWindow} instance exists.</b>
     * </p>
     *
     * @return {@code true} {@link MainWindow} exists and is available via {@link #getInstance()},
     *         {@code false} {@link MainWindow} is not instantiated and will be instantiated via
     *         {@link #getInstance()}.
     */
    public static boolean hasInstance() {
        return instance != null;
    }

    public TermLabelVisibilityManager getVisibleTermLabels() {
        return termLabelMenu.getVisibleTermLabels();
    }

    /**
     * Workaround to an issue with the Gnome window manager. This sets the application title in the
     * app menu (in the top bar) to "KeY" instead of the full class name ("de-uka-ilkd...."). This
     * should not have a negative effect on other window managers. See
     * <a href="http://elliotth.blogspot.de/2007/02/fixing-wmclass-for-your-java.html"> here</a> for
     * details.
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
     * Tries to set the configured look and feel if the option is activated.
     */
    private void setLaF() {
        try {
            String className =
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getLookAndFeel();
            // only set look and feel if configured
            // (previous KeY versions stored [no value set] as "null")
            if (className != null && !className.equals("null")) {
                UIManager.setLookAndFeel(className);

                // Workarounds for GTK+
                // TODO: check whether they apply to other LaFs
                UIManager.put("Slider.paintValue", Boolean.FALSE);
                UIManager.put("Menu.background", Color.GRAY); // menu background is still white....

                SwingUtilities.updateComponentTreeUI(this);
            }
        } catch (Exception e) {
            LOGGER.error("failed to set look and feel ", e);
        }
    }

    /**
     * Returns the MainWindow KeyMediator.
     *
     * @param userInterface The UserInterfaceControl.
     */
    private KeYMediator getMainWindowMediator(AbstractMediatorUserInterfaceControl userInterface) {
        KeYMediator result = new KeYMediator(userInterface);
        // Not sure if this is needed.
        // Automode stopped is always fired next and sets it as well (does not cause a duplicate
        // listener).
        result.addKeYSelectionListener(proofListener);
        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
        // No functionality is allowed in this method body!
        result.getUI().getProofControl().addAutoModeListener(proofListener);
        result.addGUIListener(new MainGUIListener());
        return result;
    }

    public CControl getDockControl() {
        return dockControl;
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
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().getTacletFilter();
        userInterface.getProofControl().setMinimizeInteraction(stupidMode);

        // set up actions
        openFileAction = new OpenFileAction(this);
        openSingleJavaFileAction = new OpenSingleJavaFileAction(this);
        openExampleAction = new OpenExampleAction(this);
        openMostRecentFileAction = new OpenMostRecentFileAction(this);
        editMostRecentFileAction = new EditMostRecentFileAction(this);
        saveFileAction = new SaveFileAction(this);
        saveBundleAction = new SaveBundleAction(this);
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
        goalSelectAboveAction = new GoalSelectAboveAction(this);
        goalSelectBelowAction = new GoalSelectBelowAction(this);
        SelectionHistory history = new SelectionHistory(mediator);
        selectionBackAction = new SelectionBackAction(this, history);
        selectionForwardAction = new SelectionForwardAction(this, history);
        history.addChangeListener(selectionBackAction);
        history.addChangeListener(selectionForwardAction);
        selectionBackAction.update();
        selectionForwardAction.update();

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
        toolBarPanel.add(createNavigationToolBar());

        KeYGuiExtensionFacade.createToolbars(this).forEach(toolBarPanel::add);

        getContentPane().add(toolBarPanel, BorderLayout.PAGE_START);

        proofListView.setPreferredSize(new java.awt.Dimension(350, 100));
        GuiUtilities.paintEmptyViewComponent(proofListView, "Proofs");

        // JSplitPane leftPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, proofListView,
        // mainWindowTabbedPane);
        // leftPane.setName("leftPane");
        // leftPane.setOneTouchExpandable(true);

        // JPanel rightPane = new JPanel();
        // rightPane.setLayout(new BorderLayout());
        // rightPane.add(mainFrame, BorderLayout.CENTER);
        mainFrame.add(sequentViewSearchBar, BorderLayout.SOUTH);

        // JSplitPane pane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, rightPane, sourceView);
        // pane.setResizeWeight(0.5);
        // pane.setOneTouchExpandable(true);
        // pane.setName("split2");

        // JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftPane, pane);
        // splitPane.setResizeWeight(0); // the right pane is more important
        // splitPane.setOneTouchExpandable(true);
        // splitPane.setName("splitPane");
        // getContentPane().add(splitPane, BorderLayout.CENTER);

        dockControl.putProperty(StackDockStation.TAB_PLACEMENT, TabPlacement.TOP_OF_DOCKABLE);

        getContentPane().add(dockControl.getContentArea());

        dockProofListView = DockingHelper.createSingleDock("Loaded Proofs", proofListView,
            TaskTree.class.getName());
        dockSequent = DockingHelper.createSingleDock("Sequent", mainFrame);
        dockSourceView = DockingHelper.createSingleDock("Source", sourceViewFrame);

        Stream<TabPanel> extensionPanels = KeYGuiExtensionFacade.getAllPanels(this);
        Stream<TabPanel> defaultPanels =
            Stream.of(proofTreeView, infoView, strategySelectionView, openGoalsView);
        Stream.concat(defaultPanels, extensionPanels).map(DockingHelper::createSingleDock)
                .forEach(dockControl::addDockable);
        dockControl.addDockable(dockProofListView);
        dockControl.addDockable(dockSequent);
        dockControl.addDockable(dockSourceView);

        dockProofListView.setVisible(true);
        dockSequent.setVisible(true);

        dockSourceView.setVisible(true);

        KeYGuiExtensionFacade.getAllPanels(this)
                .forEach(it -> DockingHelper.addLeftPanel(it.getClass().getName()));
        DockingHelper.restoreFactoryDefault(this);

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
        fileOperations.setFloatable(false);
        fileOperations.add(openFileAction);
        fileOperations.add(openMostRecentFileAction);
        fileOperations.add(editMostRecentFileAction);
        fileOperations.add(saveFileAction);
        fileOperations.add(saveBundleAction);
        fileOperations.addSeparator();
        fileOperations.add(proofManagementAction);

        return fileOperations;
    }

    private JToolBar createProofControlToolBar() {
        JToolBar toolBar = new JToolBar("Proof Control");
        toolBar.setFloatable(false);
        toolBar.setRollover(true);

        toolBar.add(createWiderAutoModeButton());
        toolBar.addSeparator();
        toolBar.addSeparator();
        toolBar.addSeparator();
        DropdownSelectionButton comp = createSMTComponent();
        toolBar.add(comp.getActionComponent());
        toolBar.add(comp.getSelectionComponent());
        toolBar.addSeparator();
        toolBar.add(new GoalBackAction(this, false));
        toolBar.add(new PruneProofAction(this));
        var act = new ActionHistoryExtension(this, mediator);
        toolBar.add(act.getUndoButton().getAction());
        toolBar.add(act.getUndoUptoButton());
        toolBar.addSeparator();

        return toolBar;
    }

    private JToolBar createNavigationToolBar() {
        JToolBar toolBar = new JToolBar("Selection Navigation");
        toolBar.setFloatable(false);
        toolBar.setRollover(true);

        SelectionHistory history = new SelectionHistory(mediator);
        toolBar.add(selectionBackAction);
        toolBar.add(selectionForwardAction);
        toolBar.addSeparator();

        return toolBar;
    }

    /**
     * Create the {@link #smtComponent} for selecting SMT solvers.
     *
     * @return the {@link #smtComponent}
     */
    private DropdownSelectionButton createSMTComponent() {
        smtComponent = new DropdownSelectionButton(TOOLBAR_ICON_SIZE);
        noSolverSelected = new DropdownSelectionButton.EmptyAction(true);
        noSolverSelected.setText("SMT");
        noSolverSelected.setToolTip("Choose at least one SMT solver to run");
        // Configure the smtComponent's empty item (this is selected if no solvers are available):
        String noneAvailableText = "No solver available";
        String noneAvailableTip = "<html>No SMT solver is applicable for KeY.<br>"
            + "<br>If a solver is installed on your system,"
            + "<br>please configure the KeY-System accordingly:" + System.lineSeparator()
            + "<br>Options | SMT Solvers</html>";
        smtComponent.setEmptyItem(noneAvailableText, noneAvailableTip);

        // Prepend "Run" to the currently selected action in the smtComponent
        smtComponent.setPrefix("Run ");

        /*
         * Add a ChangeListener to the smtComponent that sets the active solver union of the
         * settings to the currently selected one (if the selected action is an SMTInvokeAction).
         */
        smtComponent.addListener(e -> {
            DropdownSelectionButton but = (DropdownSelectionButton) e.getSource();
            if (but.getAction() instanceof SMTInvokeAction) {
                SMTInvokeAction action = (SMTInvokeAction) but.getAction();
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                        .setActiveSolverUnion(action.getSolverUnion());
            }
        });

        /*
         * Add a ChangeListener to the smtComponent that checks whether currently no solvers are
         * selected, but solvers are available (<-> noSolverSelected is the selected action, see
         * collapseChoice for that).
         */
        smtComponent.addListener(c -> {
            if (smtComponent.getAction() == noSolverSelected) {
                // Make sure the tooltip and text are shown.
                noSolverSelected.putValue(Action.NAME, noSolverSelected.toString());
                noSolverSelected.putValue(Action.SHORT_DESCRIPTION, noSolverSelected.getToolTip());
                boolean selectionEnabled = smtComponent.getSelectionComponent().isEnabled();
                // Disable the action button.
                smtComponent.setEnabled(false);
                // Disabling the action button also disables the selection button,
                // so enable that again (if it was before).
                smtComponent.getSelectionComponent().setEnabled(selectionEnabled);
            }
        });

        // The selectAll button of the dropdown menu, this can be reused instead of creating
        // it anew every time.
        selectAll = new JCheckBoxMenuItem("Select All");
        selectAll.setFocusPainted(false);
        selectAll.setEnabled(true);
        separator = new JSeparator();

        // Update the smtComponent with the currently (on start) available SMT solvers.
        updateSMTSelectMenu();
        mediator.addKeYSelectionListener(new DPEnableControl());
        return smtComponent;
    }

    private JComponent createWiderAutoModeButton() {
        JButton b = new JButton(autoModeAction);
        b.putClientProperty("hideActionText", Boolean.TRUE);
        // the following rigmarole is to make the button slightly wider
        JPanel p = new JPanel();
        p.setLayout(new GridBagLayout());
        p.add(b);
        return p;
    }

    /**
     * @return the status line object
     */
    MainStatusLine getStatusLine() {
        return statusLine;
    }

    public void setStatusLine(String status) {
        ThreadUtilities.invokeOnEventQueue(() -> statusLine.setStatusText(status));
    }

    private void setStandardStatusLineImmediately() {
        statusLine.reset();
    }

    /**
     * Make the status line display a standard message, make progress bar and abort button invisible
     */
    public void setStandardStatusLine() {
        ThreadUtilities.invokeOnEventQueue(this::setStandardStatusLineImmediately);
    }

    private void setStatusLineImmediately(String str, int max) {
        // statusLine.reset();
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
        ThreadUtilities.invokeOnEventQueue(() -> setStatusLineImmediately(str, max));
    }

    /**
     * Freeze the main window by blocking all input events, except those for the toolbar (i.e.
     * the abort button within the toolbar)
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
        menuBar.add(createProofMenu(null));
        menuBar.add(createOptionsMenu());
        KeYGuiExtensionFacade.addExtensionsToMainMenu(this, menuBar);
        menuBar.add(Box.createHorizontalGlue());
        menuBar.add(createHelpMenu());

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
        fileMenu.add(saveBundleAction);
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
        if (Main.isExperimentalMode()) {
            RunAllProofsAction runAllProofsAction = new RunAllProofsAction(this);
            submenu.add(runAllProofsAction);
        }
        fileMenu.addSeparator();
        fileMenu.add(recentFileMenu.getMenu());
        fileMenu.addSeparator();
        fileMenu.add(exitMainAction);
        return fileMenu;
    }

    private JMenu createViewMenu() {
        JMenu view = new JMenu("View");
        view.setMnemonic(KeyEvent.VK_V);

        view.add(new JCheckBoxMenuItem(new PrettyPrintToggleAction(this)));
        view.add(new JCheckBoxMenuItem(unicodeToggleAction));
        view.add(new JCheckBoxMenuItem(new SyntaxHighlightingToggleAction(this)));
        view.add(termLabelMenu);
        view.add(new JCheckBoxMenuItem(hidePackagePrefixToggleAction));
        view.add(new JCheckBoxMenuItem(toggleSequentViewTooltipAction));
        view.add(new JCheckBoxMenuItem(toggleSourceViewTooltipAction));

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

        view.add(createSelectionMenu());

        view.addSeparator();
        view.add(selectionBackAction);
        view.add(selectionForwardAction);
        view.addSeparator();

        return view;
    }

    private JMenu createSelectionMenu() {
        JMenu goalSelection = new JMenu("Select Goal");
        goalSelection.add(goalSelectAboveAction);
        goalSelection.add(goalSelectBelowAction);
        return goalSelection;
    }

    /**
     * Create the proof menu.
     *
     * @param selected a specific proof that the menu should work on, may be null
     * @return the menu
     */
    public JMenu createProofMenu(Proof selected) {
        JMenu proof = new JMenu("Proof");
        proof.setMnemonic(KeyEvent.VK_P);

        if (selected == null) {
            proof.add(autoModeAction);
            GoalBackAction goalBack = new GoalBackAction(this, true);
            proof.addMenuListener(new MenuListener() {
                @Override
                public void menuSelected(MenuEvent e) {
                    /*
                     * we use this MenuListener to update the name only if the menu is shown since
                     * it
                     * would be slower to update the name (which means scanning all open and closed
                     * goals) at every selection change (via the KeYSelectionListener in
                     * GoalBackAction)
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
        }
        proof.add(new AbandonTaskAction(this, selected));
        if (selected == null) {
            proof.addSeparator();
            proof.add(new SearchInProofTreeAction(this));
            proof.add(new SearchInSequentAction(this, sequentViewSearchBar));
            proof.add(new SearchNextAction(this, sequentViewSearchBar));
            proof.add(new SearchPreviousAction(this, sequentViewSearchBar));
            JMenu searchModeMenu = new JMenu("Search Mode");

            for (SequentViewSearchBar.SearchMode mode : SequentViewSearchBar.SearchMode.values()) {
                searchModeMenu.add(new SearchModeChangeAction(this, sequentViewSearchBar, mode));
            }

            proof.add(searchModeMenu);
        }
        proof.addSeparator();
        proof.add(new ShowUsedContractsAction(this, selected));
        proof.add(new ShowActiveTactletOptionsAction(this, selected));
        proof.add(showActiveSettingsAction);
        proof.add(new ShowProofStatistics(this, selected));
        proof.add(new ShowKnownTypesAction(this, selected));
        proof.addSeparator();
        proof.add(new MakeNamedFormulaToAbbrevAction(this));
        proof.addSeparator();
        return proof;
    }

    private JMenu createOptionsMenu() {
        JMenu options = new JMenu("Options");
        options.setMnemonic(KeyEvent.VK_O);

        options.add(SettingsManager.getInstance().getActionShowSettings(this));
        options.add(new TacletOptionsAction(this));
        options.add(new SMTOptionsAction(this));
        // options.add(setupSpeclangMenu()); // legacy since only JML supported
        options.addSeparator();
        options.add(new JCheckBoxMenuItem(new ToggleConfirmExitAction(this)));
        options.add(new JCheckBoxMenuItem(new AutoSave(this)));
        options.add(new MinimizeInteraction(this));
        options.add(new JCheckBoxMenuItem(new RightMouseClickToggleAction(this)));
        options.add(new JCheckBoxMenuItem(new EnsureSourceConsistencyToggleAction(this)));

        return options;

    }

    private JMenu createHelpMenu() {
        JMenu help = new JMenu("About");
        help.setMnemonic(KeyEvent.VK_A);

        help.add(new AboutAction(this));
        help.add(new KeYProjectHomepageAction(this));
        // help.add(new SystemInfoAction(this));
        help.add(new MenuSendFeedackAction(this));
        help.add(new LicenseAction(this));
        return help;
    }

    /**
     * Update the selection menu for decision procedures using SMT solvers. Remove those SMT
     * solvers, that are not installed anymore, add those, that got installed.
     */
    public void updateSMTSelectMenu() {
        Collection<SolverTypeCollection> solverUnions = ProofIndependentSettings.DEFAULT_INSTANCE
                .getSMTSettings().getUsableSolverUnions(Main.isExperimentalMode());

        if (solverUnions == null || solverUnions.isEmpty()) {
            updateDPSelectionMenu();
        } else {
            updateDPSelectionMenu(solverUnions);
        }

    }

    private void updateDPSelectionMenu() {
        /*
         * No solvers available -> this leads to the empty item of the smtComponent being set. Thus,
         * the smtComponent will be deactivated until solvers become available.
         */
        smtComponent.setItems(null, actions -> null, 0);
    }

    private void updateDPSelectionMenu(Collection<SolverTypeCollection> unions) {
        int size = unions.size();
        SMTInvokeAction[] actions = new SMTInvokeAction[size];

        // create SMTInvokeActions for the given solver unions.
        int i = 0;
        for (SolverTypeCollection union : unions) {
            SMTInvokeAction action = new SMTInvokeAction(union, this);
            actions[i] = action;
            i++;
        }

        // Set the new selection items of the smtComponent.
        smtComponent.setItems(actions, collapseChoice, actions.length);

        // If more than one action can be selected, add the selectAll-button.
        if (actions.length > 1) {
            // The old selection listener is not needed anymore.
            if (selectAllListener != null) {
                smtComponent.removeListener(selectAllListener);
            }
            smtComponent.addComponent(separator);
            smtComponent.addComponent(selectAll);
            selectAll.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    if (selectAll.isSelected()) {
                        smtComponent.selectMaxNumber();
                    } else {
                        smtComponent.deselectAll();
                    }
                }
            });
            /*
             * Set this stuff anew because for some reason it is not displayed anymore after setting
             * the action?
             */
            selectAll.setText("Select All");
            selectAll.setToolTipText("(De)select all menu items by (un)checking this");
            // Don't close the smtComponent's menu when clicking selectAll
            selectAll.putClientProperty("CheckBoxMenuItem.doNotCloseOnMouseClick", Boolean.TRUE);
            // The new selection listener checking whether all the current items or none of them
            // are selected and changing the selection status of selectAll accordingly.
            selectAllListener = e -> {
                if (smtComponent.getSelectedItems().length == actions.length
                        && !selectAll.isSelected()) {
                    selectAll.setSelected(true);
                } else if (smtComponent.getSelectedItems().length == 0
                        && selectAll.isSelected()) {
                    selectAll.setSelected(false);
                }
            };
            smtComponent.addListener(selectAllListener);
        } else {
            // If only one action is available, the selectAll button is not needed.
            smtComponent.removeComponent(selectAll);
            smtComponent.removeComponent(separator);
        }

    }

    @SuppressWarnings("unused")
    // currently not used because we only have one specification language
    private JMenuItem setupSpeclangMenu() {
        JMenu result = new JMenu("Specification Parser");
        ButtonGroup group = new ButtonGroup();
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        JRadioButtonMenuItem jmlButton =
            new JRadioButtonMenuItem("Source File Comments Are JML", gs.isUseJML());
        result.add(jmlButton);
        group.add(jmlButton);
        jmlButton.setIcon(IconFactory.jmlLogo(15));
        jmlButton.addActionListener(e -> {
            GeneralSettings gs12 = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
            gs12.setUseJML(true);
        });

        JRadioButtonMenuItem noneButton =
            new JRadioButtonMenuItem("Source File Comments Are Ignored", !gs.isUseJML());
        result.add(noneButton);
        group.add(noneButton);
        noneButton.addActionListener(e -> {
            GeneralSettings gs1 = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
            gs1.setUseJML(false);
        });

        return result;
    }

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }

    /**
     * Returns the current goal view.
     */
    public CurrentGoalView getGoalView() {
        return currentGoalView;
    }

    public void addProblem(final de.uka.ilkd.key.proof.ProofAggregate plist) {
        Runnable guiUpdater = () -> {
            disableCurrentGoalView = true;
            addToProofList(plist);
            setUpNewProof(plist.getFirstProof());
            disableCurrentGoalView = false;
            updateSequentView();
        };
        ThreadUtilities.invokeOnEventQueue(guiUpdater);
    }

    private Proof setUpNewProof(Proof proof) {
        getMediator().setProof(proof);
        return proof;
    }

    /*
     * Updates the sequent displayed in the main frame.
     */
    private synchronized void updateSequentView() {

        if (disableCurrentGoalView) {
            return;
        }

        final SequentView newSequentView;

        // if this is set we can skip calls to printSequent, since it is invoked in setSequentView
        // immediately anyways
        final boolean isPrintRunImmediately = SwingUtilities.isEventDispatchThread();
        if (getMediator().getSelectedProof() == null) {
            newSequentView = emptySequent;
        } else {
            Goal goal = getMediator().getSelectedGoal();
            if (goal != null && !goal.node().isClosed()) {
                currentGoalView.setPrinter(goal);

                if (!isPrintRunImmediately) {
                    currentGoalView.printSequent();
                }
                newSequentView = currentGoalView;
            } else {
                Sequent seq = getMediator().getSelectionModel().getSelectedSequent();
                RuleApp ruleApp = getMediator().getSelectionModel().getSelectedRuleApp();
                newSequentView = new InnerNodeView(getMediator().getSelectedProof(),
                    getMediator().getSelectedNode(), ruleApp, seq, this);
                if (!isPrintRunImmediately) {
                    newSequentView.printSequent();
                }
            }
        }

        Runnable sequentUpdater = () -> {
            mainFrame.setContent(newSequentView);
            // always does printSequent if on the event thread
            sequentViewSearchBar.setSequentView(newSequentView);
        };

        if (isPrintRunImmediately) {
            try {
                sequentUpdater.run();
            } catch (RuntimeException ex) {
                // This is a quickfix for some situations where exceptions
                // in the UI update would corrupt the entire proof state
                // such that the entire app needs to be closed. Just print
                // the exception and pretend everything was good. (Like would
                // happen when incoked on the event queue.
                LOGGER.warn("Sequent updater exception", ex);
            }
        } else {
            SwingUtilities.invokeLater(sequentUpdater);
        }

    }

    /**
     * Scroll the sequent view to the specified y coordinate.
     *
     * @param y coordinate in pixels
     */
    public void scrollTo(int y) {
        mainFrame.scrollTo(y);
    }

    void displayResults(String message) {
        setStatusLine(message);
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
     * Store the properties of the named components under {@code component} to the system
     * preferences.
     * <p>
     * This uses the {@link Preferences} class to access the system preferences. Preferences are not
     * explicitly synchronised; this happens at application end using {@link #syncPreferences()}.
     * All components which are in the component tree are queried.
     *
     * @param component the non-null component whose preferences are to be saved
     * @see PreferenceSaver
     */
    public void savePreferences(Component component) {
        prefSaver.save(component);
    }

    /**
     * Load the properties of the named components under {@code component} from the system
     * preferences.
     * <p>
     * This uses the {@link Preferences} class to access the system preferences. All components
     * which are in the component tree are queried.
     *
     * @param component the non-null component whose preferences are to be set
     * @see PreferenceSaver
     */
    public void loadPreferences(Component component) {
        prefSaver.load(component);
    }

    /**
     * Synchronised the system properties with the background storage system.
     * <p>
     * This is typically called at application termination.
     *
     * @see PreferenceSaver
     */
    public void syncPreferences() {
        try {
            prefSaver.flush();
        } catch (BackingStoreException e) {
            // it is not tragic if the preferences cannot be stored.
            LOGGER.warn("Failed to save preferences", e);
        }
    }

    /**
     * <p>
     * Returns the {@link ExitMainAction} that is used to exit the {@link MainWindow}.
     * </p>
     * <p>
     * This functionality is required because for instance other projects like the Eclipse
     * integration has to close the main window.
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
     * This functionality is required because in other project is it required to execute the
     * automatic mode without opening the result dialog which can be disabled in the
     * {@link NotificationManager}.
     * </p>
     *
     * @return
     */
    public NotificationManager getNotificationManager() {
        return notificationManager;
    }

    /**
     * A file to the menu of recent opened files.
     *
     * @see RecentFileMenu#addRecentFile(String)
     */
    public void addRecentFile(@Nonnull String absolutePath) {
        recentFileMenu.addRecentFile(absolutePath);
    }

    public void openExamples() {
        openExampleAction.actionPerformed(null);
    }

    public void loadProblem(File file) {
        getUserInterface().loadProblem(file);
    }

    public void loadProblem(File file, List<File> classPath, File bootClassPath,
            List<File> includes) {
        getUserInterface().loadProblem(file, classPath, bootClassPath, includes);
    }

    /**
     * Loads the proof with the given path from the proof bundle.
     *
     * @param proofBundle the path of the proof bundle
     * @param proofPath the path of the proof to load (relative to the root of the bundle ->
     *        filename only)
     */
    public void loadProofFromBundle(File proofBundle, File proofPath) {
        getUserInterface().loadProofFromBundle(proofBundle, proofPath);
    }

    /*
     * Retrieves supported term label names from profile and returns a sorted list of them.
     */
    public List<Name> getSortedTermLabelNames() {
        /*
         * Get list of labels from profile. This list is not always identical, since the used
         * Profile may change during execution.
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
     * Defines if taclet infos are shown or not.
     *
     * @param show {@code true} show taclet infos, {@code false} hide taclet infos.
     */
    public void setShowTacletInfo(boolean show) {
        mainFrame.setShowTacletInfo(show);
    }

    public boolean isShowTacletInfo() {
        return mainFrame.isShowTacletInfo();
    }

    public AutoModeAction getAutoModeAction() {
        return autoModeAction;
    }

    public CDockable getDockProofListView() {
        return dockProofListView;
    }

    public SingleCDockable getDockSourceView() {
        return dockSourceView;
    }

    public SingleCDockable getDockSequent() {
        return dockSequent;
    }

    public SourceViewFrame getSourceViewFrame() {
        return sourceViewFrame;
    }

    public CurrentGoalView getCurrentGoalView() {
        return currentGoalView;
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
        final Component glassPane;
        final Container contentPane;

        public GlassPaneListener(Component glassPane, Container contentPane) {
            this.glassPane = glassPane;
            this.contentPane = contentPane;
        }

        @Override
        public void mouseMoved(MouseEvent e) {
            redispatchMouseEvent(e);
        }

        /*
         * We must forward at least the mouse drags that started with mouse presses over the check
         * box. Otherwise, when the user presses the check box then drags off, the check box isn't
         * disarmed -- it keeps its dark gray background or whatever its L&F uses to indicate that
         * the button is currently being pressed.
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
                    SwingUtilities.convertPoint(glassPane, glassPanePoint, contentPane);
                Component component = SwingUtilities.getDeepestComponentAt(contentPane,
                    containerPoint.x, containerPoint.y);

                if (eventID == MouseEvent.MOUSE_PRESSED && isLiveComponent(component)) {
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
                if ((c instanceof JComponent)
                        && AUTO_MODE_TEXT.equals(((JComponent) c).getToolTipText())) {
                    return true;
                }
                c = c.getParent();
            }
            return false;
        }

        private void dispatchForCurrentComponent(MouseEvent e) {
            Point glassPanePoint = e.getPoint();
            Point componentPoint =
                SwingUtilities.convertPoint(glassPane, glassPanePoint, currentComponent);
            currentComponent.dispatchEvent(new MouseEvent(currentComponent, e.getID(), e.getWhen(),
                // do not use as it freezes the stop button: e.getModifiersEx(),
                e.getModifiers(), componentPoint.x, componentPoint.y, e.getClickCount(),
                e.isPopupTrigger()));
        }
    }

    /**
     * invoked if a frame that wants modal access is opened
     */
    class MainGUIListener implements GUIListener {

        private Set<Component> doNotReenable;

        private void enableMenuBar(JMenuBar m, boolean b) {
            for (int i = 0; i < m.getMenuCount(); i++) {
                JMenu menu = m.getMenu(i);
                if (menu != null) {
                    // otherwise it is a spacer
                    menu.setEnabled(b);
                }
            }
        }

        private void setToolBarDisabled() {
            assert EventQueue.isDispatchThread() : "toolbar disabled from wrong thread";
            doNotReenable = new LinkedHashSet<>();
            Component[] cs = controlToolBar.getComponents();
            for (Component component : cs) {
                if (!component.isEnabled()) {
                    doNotReenable.add(component);
                }
                component.setEnabled(false);
            }
            cs = fileOpToolBar.getComponents();
            for (Component c : cs) {
                if (!c.isEnabled()) {
                    doNotReenable.add(c);
                }
                c.setEnabled(false);
            }
        }

        private void setToolBarEnabled() {
            assert EventQueue.isDispatchThread() : "toolbar enabled from wrong thread";
            if (doNotReenable == null) {
                // bug #1105 occurred
                LOGGER.debug("toolbar enabled w/o prior disable");
                return;
            }

            Component[] cs = controlToolBar.getComponents();
            for (Component component : cs) {
                if (!doNotReenable.contains(component)) {
                    component.setEnabled(true);
                }
            }
            cs = fileOpToolBar.getComponents();
            for (Component c : cs) {
                if (!doNotReenable.contains(c)) {
                    c.setEnabled(true);
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
                // mainWindowTabbedPane.setEnabledForAllTabs(false);
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
                // mainWindowTabbedPane.setEnabledForAllTabs(true);
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

    class MainProofListener
            implements AutoModeListener, KeYSelectionListener, PropertyChangeListener {

        Proof proof = null;

        /**
         * focused node has changed
         */
        @Override
        public synchronized void selectedNodeChanged(KeYSelectionEvent e) {
            if (getMediator().isInAutoMode()) {
                return;
            }
            SwingUtilities.invokeLater(MainWindow.this::updateSequentView);
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public synchronized void selectedProofChanged(KeYSelectionEvent e) {
            LOGGER.debug("Main: initialize with new proof");

            if (proof != null && !proof.isDisposed()) {
                proof.getSettings().getStrategySettings().removePropertyChangeListener(this);
            }
            proof = e.getSource().getSelectedProof();
            if (proof != null) {
                proof.getSettings().getStrategySettings().removePropertyChangeListener(this);
            }

            disableCurrentGoalView = false;
            SwingUtilities.invokeLater(MainWindow.this::updateSequentView);
            makePrettyView();
        }

        /**
         * invoked if automatic execution has started
         */
        @Override
        public synchronized void autoModeStarted(ProofEvent e) {
            LOGGER.debug("Automode started");
            disableCurrentGoalView = true;
            getMediator().removeKeYSelectionListener(proofListener);
            freezeExceptAutoModeButton();
        }

        /**
         * invoked if automatic execution has stopped
         */
        @Override
        public synchronized void autoModeStopped(ProofEvent e) {
            LOGGER.debug("Automode stopped");
            unfreezeExceptAutoModeButton();
            disableCurrentGoalView = false;
            updateSequentView();
            getMediator().addKeYSelectionListenerChecked(proofListener);
        }

        @Override
        public synchronized void propertyChange(PropertyChangeEvent evt) {
            if (proof.getSettings().getStrategySettings() == evt.getSource()) {
                // updateAutoModeConfigButton();
            }
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
     * Update other UI components based on the new sequent view.
     *
     * @param sequentView the sequent view to show
     */
    public void setSequentView(SequentView sequentView) {
        sequentViewSearchBar.setSequentView(sequentView);
    }

}
