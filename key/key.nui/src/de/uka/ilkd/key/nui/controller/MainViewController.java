package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.Map;

import com.sun.javafx.collections.ObservableMapWrapper;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.Toggle;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
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
 *
 */
public class MainViewController extends NUIController {
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
    private MenuItem openProof;

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
        FileChooser fileChooser = new FileChooser();
        fileChooser.setInitialDirectory(
                new File("resources/de/uka/ilkd/key/examples"));
        FileChooser.ExtensionFilter extFilterProof = new FileChooser.ExtensionFilter(
                "Proof files", "*.proof");
        FileChooser.ExtensionFilter extFilterKey = new FileChooser.ExtensionFilter(
                "Proof files", "*.key");
        fileChooser.getExtensionFilters().add(extFilterProof);
        fileChooser.getExtensionFilters().add(extFilterKey);

        File file = fileChooser.showOpenDialog(contextMenu);

        // only load proof if any selection was made
        if (file != null) {
            // TODO Matthias will fix it!
            // Create a new tree visualizer instance for processing the
            // conversion
            // de.uka.ilkd.key.proof.Node -->
            // de.uka.ilkd.key.nui.NUI.prooftree.NUINode
            // --> TreeItem<NUINode> (JavaFX)
            Proof loadedProof = loadProof(file);
            loadedProof.setProofFile(file);

            TreeView<NUINode> proofTreeView = new TreeView<NUINode>();
            ProofTreeVisualizer proofTreeVisulizer = new ProofTreeVisualizer(
                    proofTreeView);
            proofTreeVisulizer.loadProofTree(loadedProof);
            TreeItem<NUINode> tree = proofTreeVisulizer.visualizeProofTree();

            // Store state of treeView into data model
            dataModel.saveTreeViewState(new TreeViewState(loadedProof, tree),
                    file.getName());
        }
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
    protected final void handleCloseWindow(final ActionEvent e) {
        Platform.exit();
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

    @Override
    protected void init() {

    }

    public void updateStatusbar(String text) {
        if (text != null) {
            statustext.setText(text);
        }

    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(final File proofFileName) {
        try {
            final KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFileName, null, null,
                    null, true);
            final Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            // TODO exception handling
            e.printStackTrace();
            return null;
        }
    }

}
