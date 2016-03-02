package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;
import java.util.Optional;
import java.util.ResourceBundle;

import com.sun.javafx.collections.ObservableMapWrapper;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import de.uka.ilkd.key.proof.Proof;
import javafx.application.Platform;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.Toggle;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.WindowEvent;

/**
 * Controller for the main GUI which is displayed when the program was started.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 *
 */
public class MainViewController extends NUIController
        implements Initializable, Observer {
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

    /**
     * Stores the position of components added to the SplitPane. Other views can
     * listen to changes in this map and react to changes to their position.
     */
    private final ObservableMap<String, Place> placeComponent = new ObservableMapWrapper<>(
            new HashMap<>());

    /**
     * Stores the KeyEventHandlers (registered here using registerKeyListener)
     */
    private final Map<KeyCode, SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>> keyEventHandlers = new HashMap<>();

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
     * Handles all key combinations. To make this function listedn for a certain
     * key combination, it must beforehand be registered via
     * {@link registerKeyListener}. Usually <b> not to be called by
     * developers.</b>
     * 
     * see the FIXME at registerKeyListener
     * 
     * @param k
     *            the KeyEvent
     */
    public final void handleKeyPressed(final KeyEvent k) {

        // Registered Key Handlers
        SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]> e = keyEventHandlers
                .get(k.getCode());

        if (e != null) {
            for (KeyCode keyCode : e.getValue()) {
                switch (keyCode) {
                case ALT:
                    if (!k.isAltDown()) {
                        return;
                    }
                    break;
                case CONTROL:
                    if (!k.isControlDown()) {
                        return;
                    }
                    break;
                case META:
                    if (!k.isMetaDown()) {
                        return;
                    }
                    break;
                case SHIFT:
                    if (!k.isShiftDown()) {
                        return;
                    }
                    break;
                default:
                    throw new IllegalArgumentException(
                            "You submitted an illegal modifiers list for the key "
                                    + k.getCode());
                }
            }
            e.getKey().handle(k);
        }
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
        TreeViewController treeViewController = null;

        try {
            treeViewController = (TreeViewController) nui
                    .getController("treeView");
        }
        catch (ControllerNotFoundException exception) {
            exception.showMessage();
            return;
        }

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

        FileChooser.ExtensionFilter extFilter = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof");
        fileChooser.getExtensionFilters().add(extFilter);

        File file = fileChooser.showOpenDialog(contextMenu);

        // only load proof if any selection was made
        if (file != null) {
            updateStatusbar("Beweis wird geladen");
            treeViewController.loadAndDisplayProof(file);
        }

    }

    /**
     * Loads the default components of the GUI.
     */
    @Override
    public final void initialize(final URL location,
            final ResourceBundle resources) {
    }

    /**
     * This function allows to register key event handlers. After a Handler is
     * registered for a certain key or key combination, all KeyEvents of that
     * key or key combination will be transferred to that handler. <br/>
     * <b> This functionality is not yet finished and must be used
     * cautiously.</b>
     * 
     * FIXME this does not allow to register the same key with different
     * modifiers, e.g. Enter and Shift-Enter
     * 
     * @param key
     *            – the KeyCode of the primary to be listened to
     * @param modifiers
     *            – all of the modifiers that should also be pressed to
     *            trigger the Handler
     * @param handler
     *            – the handler that is to be triggered when the key or key
     *            combination is recognised
     * 
     * @throws IllegalArgumentException
     *             – that key is already in use or modifiers does not entirely
     *             consist of modifiers
     */
    public final void registerKeyListener(final KeyCode key,
            final KeyCode[] modifiers, final EventHandler<KeyEvent> handler)
                    throws IllegalArgumentException {

        if (modifiers != null) {
            for (KeyCode c : modifiers) {
                // blame the way Java Designers made Enum for the fact that I
                // cannot make the compiler do this check
                if (!c.isModifierKey()) {
                    throw new IllegalArgumentException(
                            "You submitted an illegal modifiers list for the key "
                                    + key);
                }
            }
        }
        if (keyEventHandlers.containsKey(key)) {
            // TODO this should better be done when the view is going to be
            // hidden
            // TODO this should be implemented using WeakHandles
            // this is just a workaround to make the tests work again
            unregisterKeyListener(key);
            // throw new IllegalArgumentException(
            // "The key you submitted (" + k + ") was already in use.");
        }

        keyEventHandlers.put(key,
                new SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>(
                        handler,
                        (modifiers == null) ? new KeyCode[0] : modifiers));
    }

    /**
     * Unregister a previously registered key Listener.
     * 
     * TODO eliminate this by implementing the key register using weak handles.
     * 
     * @throws IllegalArgumentException
     *             – key was never registered
     */
    public final void unregisterKeyListener(final KeyCode k)
            throws IllegalArgumentException {
        keyEventHandlers.remove(k);
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
        Alert alert = new Alert(AlertType.INFORMATION);
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
        Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle(nui.getStringFromBundle("dialogTitle"));
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
                saveProof(proof, proof.getProofFile());
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
            saveProof(loadedProof, loadedProof.getProofFile());
        }
        else {
            // open dialog with file chooser
            handleSaveProof(e);
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
        fileChooser.setTitle(nui.getStringFromBundle("fileChooserSaveTitle"));
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
        saveProof(loadedProof, selectedFile);

    }

    /**
     * Saves the proof file proof to the given File destinationFile.
     * 
     * @param proof
     *            the {@link Proof} file to be saved.
     * @param destinationFile
     *            the destination {@link File} where the proof is saved to.
     */
    protected final void saveProof(Proof proof, File destinationFile) {
        try {
            proof.saveToFile(destinationFile);
            proof.setProofFile(destinationFile);
            updateStatusbar(nui.getStringFromBundle("savedSuccessfully") + " "
                    + destinationFile.getAbsolutePath());
        }
        catch (IOException e) {
            updateStatusbar(e.getMessage());
        }
    }

    /**
     * NEW
     * 
     * @param component
     * @param place
     */
    public void placeComponent(String componentName, Place place) {
        Parent component = null;
        try {
            component = nui.getComponent(componentName);
            selectToggle(componentName, place);
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
        catch (ComponentNotFoundException e) {
            e.showMessage();
            selectToggle(componentName, Place.HIDDEN);
        }

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
                placeComponent(componentName, place);
            }
        };
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
        // cannot be closed)
        dataModel.deleteObserver(this);
    }

}
