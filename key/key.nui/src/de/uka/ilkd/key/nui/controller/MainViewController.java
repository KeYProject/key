package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.text.MessageFormat;
import java.util.HashMap;
import java.util.Observable;
import java.util.Observer;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;

import com.sun.javafx.collections.ObservableMapWrapper;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
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
        BOTTOM, HIDDEN, LEFT, MIDDLE, RIGHT
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
    final private AtomicBoolean isLoadingProof = new AtomicBoolean(false);

    /**
     * The thread that is used for the loading task.
     */
    private Thread loadingThread;

    /**
     * Includes the components which were added to the main Window
     */
    private HashMap<String, Pane> components = new HashMap<String, Pane>();

    /**
     * Stores the position of components added to the SplitPane. Other views can
     * listen to changes in this map and react to changes to their position.
     */
    private final ObservableMap<String, Place> placeComponent = new ObservableMapWrapper<>(
            new HashMap<>());

    public Menu getViewMenu() {
        return viewMenu;
    }

    /**
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
        FileChooser fileChooser = new FileChooser();

        TreeViewState loadedTVS = dataModel.getLoadedTreeViewState();
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
            fileChooser.setInitialDirectory(
                    new File("resources/de/uka/ilkd/key/examples"));
        }

        FileChooser.ExtensionFilter extFilterProof = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof");
        FileChooser.ExtensionFilter extFilterKey = new FileChooser.ExtensionFilter(
                "Proof files", "*.key");
        fileChooser.getExtensionFilters().add(extFilterProof);
        fileChooser.getExtensionFilters().add(extFilterKey);

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
     *             p == HIDDEN
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

        // enforces to show the confirmation dialog always before closing KeY
        // TODO remove this line after 2nd round of user study
        // TODO set visibility of setModified to private
        if (dataModel.getLoadedTreeViewState() != null) {
            dataModel.getLoadedTreeViewState().setModified(true);
        }

        // If no proof file was loaded OR file was not changed: close
        // application immediately
        if (dataModel.getLoadedTreeViewState() == null
                || !(dataModel.getLoadedTreeViewState().isModified())) {
            Platform.exit();
            return;
        }

        // File was changed: ask user if he wants to save changes
        // create alert window
        Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle(bundle.getString("dialogTitle"));
        alert.setHeaderText(nui.getStringFromBundle("dialogHeader"));
        String filename = dataModel.getLoadedTreeViewState().getProof()
                .getProofFile().getName();
        alert.setContentText(nui.getStringFromBundle("dialogQuestion") + " '"
                + filename + "' ?");
        alert.getButtonTypes().setAll(ButtonType.YES, ButtonType.NO,
                ButtonType.CANCEL);
        Optional<ButtonType> result = alert.showAndWait();

        if (result.get() == ButtonType.YES || result.get() == ButtonType.NO) {
            // If YES was selected: save changes made to file
            if (result.get() == ButtonType.YES) {
                Proof proof = dataModel.getLoadedTreeViewState().getProof();
                dataModel.saveProof(proof, proof.getProofFile());
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
        Proof loadedProof = dataModel.getLoadedTreeViewState().getProof();

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

        // Get loaded proof
        Proof loadedProof = dataModel.getLoadedTreeViewState().getProof();

        // Open file picker window
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle(bundle.getString("fileChooserSaveTitle"));
        // set initial directory to last saved location (if available)
        if (loadedProof.getProofFile() != null) {
            // if file has a parent directory, set initial directory
            File parentDir = loadedProof.getProofFile().getParentFile();
            if (parentDir != null) {
                fileChooser.setInitialDirectory(parentDir);
            }
        }
        FileChooser.ExtensionFilter extFilter = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof");
        fileChooser.getExtensionFilters().add(extFilter);

        File selectedFile = fileChooser.showSaveDialog(contextMenu);

        // abort save action if no selection was made in file chooser
        if (selectedFile == null) {
            return;
        }

        // save proof file
        dataModel.saveProof(loadedProof, selectedFile);

    }

    @FXML
    protected final void handleCancelLoadingProcess(final ActionEvent e) {
        cancelLoadProof();
    }

    /**
     * NEW
     * 
     * @param component
     * @param place
     */
    public void moveComponentTo(Pane component, Place place) {

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

    public void addComponent(Pane component, Place place) {
        components.put(component.getId(), component);
        moveComponentTo(component, place);
    }

    private void selectToggle(String componentName, Place place) {
        try {
            for (Toggle t : nui.getToggleGroup(componentName).getToggles()) {
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
     * @param e
     *            The ActionEvent
     */
    public EventHandler<ActionEvent> getNewHandleLoadComponent() {
        return new EventHandler<ActionEvent>() {

            @Override
            public void handle(ActionEvent e) {
                RadioMenuItem clickedItem = (RadioMenuItem) e.getSource();
                String componentName = (String) // e.g. "treeView", "proofView"
                clickedItem.getProperties().get("componentName");

                Place place;

                switch (clickedItem.getText()) {
                case "left":
                    place = Place.LEFT;
                    break;
                case "middle":
                    place = Place.MIDDLE;
                    break;
                case "right":
                    place = Place.RIGHT;
                    break;
                case "bottom":
                    place = Place.BOTTOM;
                    break;
                default:
                    place = Place.HIDDEN;
                    break;
                }
                moveComponentTo(components.get(componentName), place);
            }
        };
    }

    /**
     * Executes the given EventHandler e if any key was pressed, therefore the
     * provided Handler <b>must check by itself</b> if the right KeyCode was
     * pressed.
     * 
     * @param e
     *            The EventHandler
     */
    public void registerKeyListener(EventHandler<KeyEvent> e) {
        root.addEventHandler(KeyEvent.KEY_PRESSED, e);
    }

    /**
     * {@inheritDoc}
     */
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
    public void updateStatusbar(String text) {
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
    public void update(Observable o, Object arg) {
        // If first proof file is loaded, enable MenuItems for store action
        saveProof.setVisible(true);
        saveProofAs.setVisible(true);
        // Remove observer, because we do not need it anymore (-> proof files
        // cannot be closed without closing the application)
        dataModel.deleteObserver(this);
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

            // TODO not a very kind way to stop a thread
            // However the method KeYEnvironment.load doesn't support
            // interrupting.
            try {

                try {
                    final java.lang.reflect.Method tsm = Thread.class
                            .getDeclaredMethod("stop0",
                                    new Class[] { Object.class });
                    tsm.setAccessible(true);
                    tsm.invoke(loadingThread, new ThreadDeath());
                }
                catch (java.lang.ThreadDeath e) {
                    System.out.println(
                            "ThreadDeath to ignore? Speak with Matthias"); // TODO
                }

                // reset loading state
                Platform.runLater(new Runnable() {
                    /**
                     * {@inheritDoc}
                     */
                    @Override
                    public void run() {
                        statustext.setText("Loading has been cancelled.");
                        root.setCursor(Cursor.DEFAULT);
                        openProof.setDisable(false);
                        progressIndicator.setVisible(false);
                        cancelButton.setVisible(false);
                    }
                });
            }
            catch (NoSuchMethodException e1) {
                e1.printStackTrace();
            }
            catch (SecurityException e1) {
                e1.printStackTrace();
            }
            catch (IllegalAccessException e1) {
                e1.printStackTrace();
            }
            catch (IllegalArgumentException e1) {
                e1.printStackTrace();
            }
            catch (InvocationTargetException e1) {
                e1.printStackTrace();
            }
            catch (java.lang.ThreadDeath e) {
                System.out.println(
                        "Unexpected ThreadDeath in cancelLoadProof. Speak with Matthias."); // TODO
            }
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

                    // load proof
                    final KeYEnvironment<?> environment = KeYEnvironment.load(
                            JavaProfile.getDefaultInstance(), proofFileName,
                            null, null, null, true);
                    final Proof proof = environment.getLoadedProof();

                    proof.setProofFile(proofFileName);

                    // convert proof to fx tree
                    final ProofTreeItem fxtree = new ProofTreeConverter(proof)
                            .createFXProofTree();

                    // set Loading = false as you can no longer cancel
                    final boolean hasNotBeenCanceled = isLoadingProof
                            .compareAndSet(true, false);

                    if (hasNotBeenCanceled) {
                        // reset set gui waiting state
                        Platform.runLater(new Runnable() {
                            @Override
                            public void run() {
                                // Store state of treeView into data model.
                                dataModel.saveTreeViewState(
                                        new TreeViewState(proof, fxtree),
                                        proofFileName.getName());

                                statustext.setText("Ready.");
                                progressIndicator.setVisible(false);
                                cancelButton.setVisible(false);
                                root.setCursor(Cursor.DEFAULT);
                                openProof.setDisable(false);
                            }
                        });
                    }

                }
                catch (ProblemLoaderException e) {
                    // This Exception is thrown if the thread has been killed.
                    if (isLoadingProof.get()) {
                        // error during loading
                        System.out
                                .println("If this occurs speak with Matthias");
                        e.printStackTrace();
                    }
                    else {
                        // exception occured by thread killing (canceling)
                        System.out.println("Usual PLException...");
                    }
                }
                catch (java.lang.ThreadDeath e) {
                    System.out.println(
                            "Unexpected Thread Death in call. Talk to Matthias");
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
