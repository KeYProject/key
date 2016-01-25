package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.net.URL;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;
import com.sun.javafx.collections.ObservableMapWrapper;
import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.application.Platform;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;

/**
 * Controller for the main GUI which is displayed when the program was started.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 *
 */
public class NUIController implements Initializable {
    /**
     * Provides an enum for the available places in the main window.
     */
    public enum Place {
        BOTTOM, HIDDEN, LEFT, MIDDLE, RIGHT
    }

    /**
     * Singleton.
     */
    private static NUIController instance;

    /**
     * Implements the Singleton pattern.
     * 
     * @return the single instance of <tt>this</tt>
     */
    public static NUIController getInstance() {
        if (instance == null) {
            instance = new NUIController();
            return instance;
        }
        else {
            return instance;
        }
    }

    /**
     * Stores the KeyEventHandlers (registered here using registerKeyListener)
     */
    private Map<KeyCode, SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>> keyEventHandlers = new HashMap<>();

    /**
     * Stores the position of components added to the SplitPane. Other views can
     * listen to changes in this map and react to changes to their position.
     */
    private ObservableMap<String, Place> placeComponent = new ObservableMapWrapper<>(
            new HashMap<>());

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
    private ToggleGroup toggleGroup0;
    @FXML
    private ToggleGroup toggleGroup1;
    @FXML
    private ToggleGroup toggleGroup2;
    @FXML
    private ToggleGroup toggleGroup3;

    /**
     * Loads the default components of the GUI.
     */
    @Override
    public final void initialize(final URL location, final ResourceBundle resources) {
        // Load default components
        createOrMoveOrHideComponent(TreeViewController.NAME, Place.LEFT,
                TreeViewController.RESOURCE);
        createOrMoveOrHideComponent("proofView", Place.RIGHT, "proofView.fxml");
        Platform.runLater(() -> {
            TreeViewController t = ComponentFactory.getInstance()
                    .getController(TreeViewController.NAME);
            t.loadExampleProof();
        });

        // Select appropriate menu item entries
        final int POSITION_TREEVIEW = 3; // 3: left view
        final int POSITION_PROOFVIEW = 2; // 2: right view
        toggleGroup2.selectToggle(toggleGroup2.getToggles().get(POSITION_TREEVIEW));
        toggleGroup3.selectToggle(toggleGroup3.getToggles().get(POSITION_PROOFVIEW));

        instance = this; // TODO this is ugly
    }

    /**
     * This is the primary function used by everyone to create, move or hide
     * components.
     * 
     * @param componentName
     *            – the name of the component to create / relocate / hide,
     *            usually taken from Controller.NAME
     * @param place
     *            – the place where the Component is to be moved to
     * @param componentResource
     *            – the name of the components resource file, including the file
     *            extension. The file must be a valid fxml file placed in the
     *            resources folder.
     * @throws IllegalArgumentException
     *             The Component componentName already exists in the Place
     *             place.
     */
    public final void createOrMoveOrHideComponent(final String componentName, final Place place,
            final String componentResource) throws IllegalArgumentException {
        // Does the component already exist?
        // Then the user wants to either change its place or to hide it
        if (placeComponent.containsKey(componentName)) {
            Node existingcomponent = getPane(placeComponent.get(componentName)).getChildren()
                    .stream().filter((n) -> n.getId().equals(componentName)).findFirst().get();
            // Add Component to the respective Pane
            // and update its position in the posComponent Map.
            if (place == Place.HIDDEN) {
                // Component is to be removed, remove it.

                /*
                 * TODO Here all KeyListeners of the view to be hidden should be
                 * removed from the Register or the Register should
                 * WeakReferences
                 */
                getPane(placeComponent.get(componentName)).getChildren().remove(existingcomponent);
                placeComponent.remove(componentName);
                statustext.setText("View " + componentName + " hidden.");
                ComponentFactory.getInstance().deleteComponent(componentName);
            }
            else {
                // Component is to be moved, move it.
                getPane(place).getChildren().add(existingcomponent);
                placeComponent.replace(componentName, place);
            }
        }
        else if (place != Place.HIDDEN) {
            // Component did not already exist, thus it must be created
            placeComponent.put(componentName, place);
            Parent newComponent = ComponentFactory.getInstance().createComponent(componentName,
                    componentResource);
            getPane(place).getChildren().add(newComponent);
        }
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
                            "You submitted an illegal modifiers list for the key " + k.getCode());
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
        if (!ComponentFactory.getInstance().hasComponent(TreeViewController.NAME)) {
            statustext.setText("TreeView not found, opening a tree is not possible");
        }
        else {
            FileChooser fileChooser = new FileChooser();
            fileChooser.setInitialDirectory(new File("resources/de/uka/ilkd/key/examples"));
            FileChooser.ExtensionFilter extFilter = new FileChooser.ExtensionFilter("Proof files",
                    "*.proof");
            fileChooser.getExtensionFilters().add(extFilter);
            File file = fileChooser.showOpenDialog(contextMenu);
            // only load proof if any selection was made
            if (file != null) {
                TreeViewController t = ComponentFactory.getInstance()
                        .getController(TreeViewController.NAME);
                t.loadAndDisplayProof(file);
            }
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
     *            – all of the modifiers that should also be pressed to trigger
     *            the Handler
     * @param handler
     *            – the handler that is to be triggered when the key or key
     *            combination is recognised
     * 
     * @throws IllegalArgumentException
     *             – that key is already in use or modifiers does not entirely
     *             consist of modifiers
     */
    public final void registerKeyListener(final KeyCode key, final KeyCode[] modifiers,
            final EventHandler<KeyEvent> handler) throws IllegalArgumentException {

        if (modifiers != null) {
            for (KeyCode c : modifiers) {
                // blame the way Java Designers made Enum for the fact that I
                // cannot make the compiler do this check
                if (!c.isModifierKey()) {
                    throw new IllegalArgumentException(
                            "You submitted an illegal modifiers list for the key " + key);
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

        keyEventHandlers.put(key, new SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>(
                handler, (modifiers == null) ? new KeyCode[0] : modifiers));
    }

    /**
     * Unregister a previously registered key Listener.
     * 
     * TODO eliminate this by implementing the key register using weak handles.
     * 
     * @throws IllegalArgumentException
     *             – key was never registered
     */
    public final void unregisterKeyListener(final KeyCode k) throws IllegalArgumentException {
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
    protected final Pane getPane(final Place p) throws IllegalArgumentException {
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
     * Handles the ActionEvent resulting in the user adding, hiding or moving
     * GUI components via the View menu. Usually <b> not to be called by
     * developers. </b>
     * 
     * @param e
     *            The ActionEvent
     */
    @FXML
    protected final void handleLoadComponent(final ActionEvent e) {
        RadioMenuItem clickedItem = (RadioMenuItem) e.getSource();
        String componentName = (String) // e.g. "treeView", "proofView"
        clickedItem.getParentMenu().getProperties().get("componentName");

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

        String componentResource = (String) clickedItem.getParentMenu().getProperties()
                .get("componentResource");

        createOrMoveOrHideComponent(componentName, place, componentResource);
    }
}
