package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.text.MessageFormat;
import java.util.HashMap;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;
import com.sun.javafx.collections.ObservableMapWrapper;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.collections.ObservableMap;
import javafx.concurrent.Task;
import javafx.event.ActionEvent;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.Cursor;
import javafx.scene.Parent;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ProgressIndicator;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.Toggle;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;

/**
 * Controller for the main GUI which is displayed when the program was started.
 *
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 * @author Matthias Schultheis
 *
 */
@ControllerAnnotation(createMenu = false)
public class MainViewController extends NUIController implements Observer {

    /**
     * Provides an enum for the available places in the main window.
     */
    public enum Place {
        /**
         * Indicates that the view is placed in the bottom pane.
         */
        BOTTOM,
        /**
         * Indicates that the view is not placed in any view and thus is hidden.
         */
        HIDDEN,
        /**
         * Indicates that the view is placed in the left pane.
         */
        LEFT,
        /**
         * Indicates that the view is placed in the middle pane.
         */
        MIDDLE,
        /**
         * Indicates that the view is placed in the right pane.
         */
        RIGHT
    }

    // Definition of GUI fields
    @FXML
    private HBox bottom;
    @FXML
    private ContextMenu contextMenu;
    @FXML
    private VBox left;
    @FXML
    private VBox middle;
    @FXML
    private VBox right;
    @FXML
    private Parent root;
    @FXML
    private Label statustext;
    @FXML
    private Menu viewMenu;
    @FXML
    private MenuItem saveProofAs;
    @FXML
    private MenuItem saveProof;
    @FXML
    private MenuItem openProof;
    @FXML
    private ProgressIndicator progressIndicator;
    @FXML
    private Button cancelButton;

    /**
     * An atomic boolean to indicate if loading is in progress While this is set
     * to true, the loading task can be cancelled.
     */
    private final AtomicBoolean isLoadingProof = new AtomicBoolean(false);

    /**
     * The thread that is used for the loading task.
     */
    private Thread loadingThread;

    /**
     * Includes the components which were added to the main Window.
     */
    private final Map<String, Pane> components = new HashMap<>();

    /**
     * Stores the position of components added to the SplitPane. Other views can
     * listen to changes in this map and react to changes to their position.
     */
    private final ObservableMap<String, Place> placeComponent = new ObservableMapWrapper<>(
            new HashMap<>());

    private KeYEnvironment<DefaultUserInterfaceControl> keyEnvironment;

    /**
     * Returns the {@link #viewMenu} which contains the menu items of the menu
     * bar.
     * 
     * @return the viewMenu
     */
    public Menu getViewMenu() {
        return viewMenu;
    }

    /**
     * Returns the {@link #placeComponent} which contains the assignment from
     * components to their position.
     * 
     * @return the placeComponent
     */
    public final ObservableMap<String, Place> getPlaceComponent() {
        return placeComponent;
    }

    /**
     * Handles the ActionEvent resulting in the user clicking "Open Proof..." in
     * the File menu. Usually <b> not to be called by developers. </b>
     *
     * @param e
     *            The ActionEvent
     */
    @FXML
    public final void handleOpenProof(final ActionEvent e) {
        final FileChooser fileChooser = new FileChooser();

        final TreeViewState loadedTVS = dataModel.getLoadedTreeViewState();
        // set default directory to location where currently loaded proof is
        // located
        File parentDirectory = null;
        if (dataModel.getLoadedTreeViewState() != null) {
            parentDirectory = loadedTVS.getProof().getProofFile()
                    .getParentFile();
        }
        if (parentDirectory != null) {
            fileChooser.setInitialDirectory(parentDirectory);
        }
        // if no proof is loaded, use the example directory (default)
        else {
            final File jarFile = new File(getClass().getProtectionDomain()
                    .getCodeSource().getLocation().getPath());
            if (!jarFile.isFile()) { // one for gui tests, while running
                                     // application in ide
                fileChooser.setInitialDirectory(
                        new File("resources/de/uka/ilkd/key/examples"));
            }
        }

        final FileChooser.ExtensionFilter extFilterProof = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof", "*.key");
        fileChooser.getExtensionFilters().add(extFilterProof);
        final File file = fileChooser.showOpenDialog(contextMenu);

        // only load proof if any selection was made
        if (file != null) {
            loadProof(file);
        }
    }

    /**
     * Returns the Pane where all the Components in the Place p are stored.
     *
     * @param p
     *            a {@link Place}
     * @return the respective Pane
     * @throws IllegalArgumentException
     *             if (p == HIDDEN) holds
     */
    public final Pane getPane(final Place p) throws IllegalArgumentException {
        switch (p) {
        case MIDDLE:
            return middle;
        case BOTTOM:
            return bottom;
        case LEFT:
            return left;
        case RIGHT:
            return right;
        default:
            throw new IllegalArgumentException();
        }
    }

    /**
     * Handles the ActionEvent resulting in the user clicking "About KeY" in the
     * About menu. Usually <b> not to be called by developers. </b>
     *
     * @param e
     *            The ActionEvent
     */
    @FXML
    protected void handleAboutWindow(final ActionEvent e) {
        final Alert alert = new Alert(AlertType.INFORMATION);
        alert.setTitle("KeY");
        alert.setHeaderText("KeY");
        alert.setContentText("Version: Bachelor Praktikum Gruppe 10");
        alert.showAndWait();
    }

    /**
     * Handles the ActionEvent resulting in the user clicking "Close" in the
     * File menu. Usually <b> not to be called by developers. </b>
     *
     * @param e
     *            The ActionEvent
     */
    @FXML
    public final void handleCloseWindow(final Event e) {
        // If no proof file was loaded OR file was not changed: close
        // application immediately
        if (dataModel.getLoadedTreeViewState() == null
                || !(dataModel.getLoadedTreeViewState().isModified())) {
            Platform.exit();
            return;
        }

        // File was changed: ask user if he wants to save changes
        // create alert window
        final Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle(bundle.getString("dialogTitle"));

        // --- define text for header and content area
        final String filename = dataModel.getLoadedTreeViewState().getProof()
                .getProofFile().getName();
        alert.setHeaderText(MessageFormat.format(
                bundle.getString("dialogHeader"), "'" + filename + "'"));
        alert.setContentText(bundle.getString("dialogQuestion"));

        // --- define button types
        final ButtonType buttonSaveAs = new ButtonType(
                bundle.getString("dialogSaveAs"));
        final ButtonType buttonClose = new ButtonType(
                bundle.getString("dialogExit"));
        final ButtonType buttonAbort = new ButtonType(
                bundle.getString("dialogAbort"));
        alert.getButtonTypes().setAll(buttonSaveAs, buttonClose, buttonAbort);

        final Optional<ButtonType> result = alert.showAndWait();
        if (result.get() == buttonSaveAs || result.get() == buttonClose) {
            // If YES was selected: save changes made to file
            if (result.get() == buttonSaveAs) {
                handleSaveProofAs(null);
            }
            // Close application without saving
            Platform.exit();
        }

        // If CANCEL was selected (or in any other case): do not close KeY
        alert.close();
        e.consume();
    }

    /**
     * Handles saving of a proof file if no destination path is specified. Uses
     * the location where the proof was saved to the last time.
     *
     * @param e
     *            the ActionEvent raised by clicking on the MenuItem.
     */
    @FXML
    protected final void handleSaveProof(final ActionEvent e) {
        // retrieve last saved location from proof file
        final Proof loadedProof = dataModel.getLoadedTreeViewState().getProof();

        if (loadedProof != null && loadedProof.getProofFile() != null) {
            // call saveProof with proof file
            dataModel.saveProof(loadedProof, loadedProof.getProofFile());
        }
        else {
            // open dialog with file chooser
            handleSaveProofAs(e);
        }
    }

    /**
     * Handles saving of a proof file if the destination path should be
     * specified. Opens a file chooser dialog where the path can be chosen.
     *
     * @param e
     *            the ActionEvent raised by clicking on the MenuItem.
     */
    @FXML
    protected final void handleSaveProofAs(final ActionEvent e) {
        saveProofAsDialog();
    }

    /**
     * Shows a save dialog with a file chooser.
     */
    public void saveProofAsDialog() {
        // Get loaded proof
        final Proof loadedProof = dataModel.getLoadedTreeViewState().getProof();

        // Open file picker window
        final FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle(bundle.getString("fileChooserSaveTitle"));
        // set initial directory to last saved location (if available)
        if (loadedProof.getProofFile() != null) {
            // if file has a parent directory, set initial directory
            final File parentDir = loadedProof.getProofFile().getParentFile();
            if (parentDir != null) {
                fileChooser.setInitialDirectory(parentDir);
            }
        }
        final FileChooser.ExtensionFilter extFilter = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof");
        fileChooser.getExtensionFilters().add(extFilter);

        final File selectedFile = fileChooser.showSaveDialog(contextMenu);

        // save proof file if any destination was specified
        if (selectedFile != null) {
            dataModel.saveProof(loadedProof, selectedFile);
        }
    }

    /**
     * Handles canceling the proof loading process.
     * 
     * @param e
     *            the ActionEvent raised by clicking on the cancel loading
     *            button.
     */
    @FXML
    protected final void handleCancelLoadingProcess(final ActionEvent e) {
        cancelLoadProof();
    }

    /**
     * Moves the Pane component to the position specified by place.
     *
     * @param component
     *            The component to be moved.
     * @param place
     *            The position where the component should be moved to.
     */
    private void moveComponentTo(final Pane component, final Place place) {
        selectToggle(component.getId(), place);
        if (place == Place.HIDDEN) {
            component.setVisible(false);
            nui.getRoot().getChildren().remove(component);
        }
        else {
            component.setVisible(true);
            if (!getPane(place).getChildren().contains(component))
                getPane(place).getChildren().add(component);
        }
    }

    /**
     * Moves the Pane component to the position specified by place. Additionally
     * to {@link #moveComponentTo(Pane, Place)} it stores the added component in
     * the list of {@link #components}.
     * 
     * @param component
     *            The component to be moved.
     * @param place
     *            The position where the component should be moved to.
     */
    public void addComponent(final Pane component, final Place place) {
        components.put(component.getId(), component);
        moveComponentTo(component, place);
    }

    /**
     * Marks the element of the toggle group as selected, according to the given
     * componentName and the specified place.
     * 
     * @param componentName
     *            The component whose toggle should be updated.
     * @param place
     *            The new position of the component.
     */
    private void selectToggle(final String componentName, final Place place) {
        try {
            for (final Toggle t : nui.getToggleGroup(componentName)
                    .getToggles()) {
                if (t.getUserData().equals(place)) {
                    t.setSelected(true);
                }
            }
        }
        catch (ToggleGroupNotFoundException e) {
            e.showMessage();
        }
    }

    /**
     * Handles the ActionEvent resulting in the user adding, hiding or moving
     * GUI components via the View menu. Usually <b> not to be called by
     * developers. </b>
     * 
     * @return EventHandler<ActionEvent> The action event associated with the
     *         clicked menu entry.
     */
    public EventHandler<ActionEvent> getNewHandleLoadComponent() {
        return ((actionEvent) -> {
            final RadioMenuItem clickedItem = (RadioMenuItem) actionEvent
                    .getSource();
            // e.g. "treeView", "proofView"
            final String componentName = (String) clickedItem.getProperties()
                    .get("componentName");
            final String clickedText = clickedItem.getText();
            Place place;

            if (clickedItem.getText().equals(bundle.getString("left"))) {
                place = Place.LEFT;
            }
            else if (clickedText.equals(bundle.getString("middle"))) {
                place = Place.MIDDLE;
            }
            else if (clickedText.equals(bundle.getString("right"))) {
                place = Place.RIGHT;
            }
            else if (clickedText.equals(bundle.getString("bottom"))) {
                place = Place.BOTTOM;
            }
            else {
                place = Place.HIDDEN;
            }
            moveComponentTo(components.get(componentName), place);
        });
    }

    /**
     * Executes the given EventHandler e if any key was pressed, therefore the
     * provided Handler <b>must check by itself</b> if the right KeyCode was
     * pressed.
     *
     * @param e
     *            The EventHandler
     */
    public void registerKeyListener(final EventHandler<KeyEvent> e) {
        root.addEventHandler(KeyEvent.KEY_PRESSED, e);
    }

    @Override
    protected void init() {
        dataModel.addObserver(this);
    }

    /**
     * Updates the status bar on the mainView by the given text. Keeps the text
     * on the status bar till the next update is performed.
     *
     * @param text
     *            String to be set to the status bar.
     */
    public void updateStatusbar(final String text) {
        if (text != null) {
            statustext.setText(text);
        }
    }

    /**
     * Updates the MainView if any change in the dataModel occurred.
     *
     * @param o
     *            The observable, here the dataModel
     * @param arg
     *            An argument (not used)
     */
    @Override
    public void update(final Observable o, final Object arg) {
        if (dataModel.getLoadedTreeViewState() == null) {
            saveProof.setVisible(false);
            saveProofAs.setVisible(false);
        }
        else {
            saveProof.setVisible(true);
            saveProofAs.setVisible(true);
        }
    }

    /**
     * Invokes canceling of proof loading process. If no proof is loaded at the
     * moment, nothing is done.
     */
    private void cancelLoadProof() {

        // try to set loading status atomically
        final boolean hasBeenCanceled = isLoadingProof.compareAndSet(true,
                false);
        if (hasBeenCanceled) {
            /*
             * Not a very kind way to stop a thread However the method
             * KeYEnvironment.load doesn't support interrupting
             */
            try {
                java.lang.reflect.Method tsm = Thread.class.getDeclaredMethod(
                        "stop0", new Class[] { Object.class });
                tsm.setAccessible(true);
                tsm.invoke(loadingThread, new ThreadDeath());
            }
            catch (NoSuchMethodException | SecurityException
                    | IllegalAccessException | IllegalArgumentException
                    | InvocationTargetException e) {
                // Exception can be ignored, because KeYEnvironment object will
                // be re-created by next proof loading
            }

            // reset loading state
            Platform.runLater(() -> {
                statustext.setText("Loading has been cancelled.");
                root.setCursor(Cursor.DEFAULT);
                openProof.setDisable(false);
                progressIndicator.setVisible(false);
                cancelButton.setVisible(false);
            });
        }

    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     */
    private void loadProof(final File proofFileName) {

        // Create a new tree visualizer instance for processing the
        // conversion
        // de.uka.ilkd.key.proof.Node -->
        // de.uka.ilkd.key.nui.NUI.prooftree.NUINode
        // --> ProofTreeItem (JavaFX)

        statustext.setText(MessageFormat.format(
                bundle.getString("statusLoading"), proofFileName.getName()));
        progressIndicator.setVisible(true);
        cancelButton.setVisible(true);
        root.setCursor(Cursor.WAIT);
        openProof.setDisable(true);

        // define a task for proof loading to do it asynchronously
        final Task<Void> task = new Task<Void>() {

            @Override
            public Void call() throws InterruptedException {

                try {
                    // set Loading = false to enable canceling
                    isLoadingProof.set(true);

                    // important to initialize KeYEnvironment
                    final MainWindow mainWindow = MainWindow.getInstance();
                    mainWindow.setVisible(false);
                    // load proof
                    System.out.println("Start loading proof: " + proofFileName);

                    // Load proof
                    DefaultUserInterfaceControl ui = new DefaultUserInterfaceControl(
                            null);
                    AbstractProblemLoader loader = ui.load(null, proofFileName,
                            null, null, null, null, false);
                    InitConfig initConfig = loader.getInitConfig();
                    keyEnvironment = new KeYEnvironment<DefaultUserInterfaceControl>(
                            ui, initConfig, loader.getProof(),
                            loader.getResult());
                    /*
                     * final KeYEnvironment<?> environment =
                     * KeYEnvironment.load( JavaProfile.getDefaultInstance(),
                     * proofFileName, null, null, null, true);
                     * 
                     * final Proof proof = environment.getLoadedProof();
                     */
                    final Proof proof = keyEnvironment.getLoadedProof();
                    proof.setProofFile(proofFileName);

                    System.out.println("loading finished!");

                    // convert proof to fx tree
                    final ProofTreeItem fxtree = new ProofTreeConverter(proof)
                            .createFXProofTree();

                    // set Loading = false as you can no longer cancel
                    final boolean hasNotBeenCanceled = isLoadingProof
                            .compareAndSet(true, false);

                    if (hasNotBeenCanceled) {
                        // reset set gui waiting state
                        Platform.runLater(() -> {
                            // Store state of treeView into data model.
                            dataModel.saveTreeViewState(
                                    new TreeViewState(proof, fxtree),
                                    proofFileName.getName());

                            statustext.setText("Ready.");
                            progressIndicator.setVisible(false);
                            cancelButton.setVisible(false);
                            root.setCursor(Cursor.DEFAULT);
                            openProof.setDisable(false);
                        });
                    }

                }
                catch (ProblemLoaderException | java.lang.ThreadDeath e) {
                    // This Exception is thrown if the thread has been killed
                    // and can thus be ignored.
                }
                return null;
            }

        };

        // execute loading in a new thread
        loadingThread = new Thread(task);
        loadingThread.setDaemon(true);
        loadingThread.start();
    }

}
