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
import javafx.beans.InvalidationListener;
import javafx.beans.property.ObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuButton;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;

/**
 * Controller for the main GUI which is displayed when the program was started
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 *
 */
public class NUIController implements Initializable {
    /**
     * Stores the position of components added to the SplitPane
     */
    private ObservableMap<String, Place> placeComponent = new ObservableMapWrapper<>(new HashMap<>());

    /**
     * Provides an enum for the available places to avoid
     * hard-to-find-typo-bugs.
     */
    public enum Place {
        LEFT, MIDDLE, RIGHT, BOTTOM, HIDDEN
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
     * @return the placeComponent
     */
    public final ObservableMap<String, Place> getPlaceComponent() {
        return placeComponent;
    }

    // Definition of GUI fields
    @FXML
    VBox left;
    @FXML
    VBox middle;
    @FXML
    VBox right;
    @FXML
    HBox bottom;
    @FXML
    Parent root;
    @FXML
    Label statustext;
    @FXML
    ContextMenu contextMenu;
    @FXML
    MenuButton ButtonProofView;
    @FXML
    MenuButton ButtonGoalView;
    @FXML
    MenuButton ButtonOpenProofsView;
    @FXML
    MenuButton ButtonTreeView;
    @FXML
    ToggleGroup toggleGroup0;
    @FXML
    ToggleGroup toggleGroup1;
    @FXML
    ToggleGroup toggleGroup2;
    @FXML
    ToggleGroup toggleGroup3;

    /**
     * Loads the default components of the GUI
     */
    @Override
    public void initialize(final URL location, final ResourceBundle resources) {
        // Load default components
        createOrMoveOrHideComponent("treeView", Place.LEFT, "treeView.fxml");
        createOrMoveOrHideComponent("proofView", Place.RIGHT, "proofView.fxml");
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                TreeViewController t = ComponentFactory.getInstance().getController("treeView");
                t.loadExampleProof();
            }
        });
        // Select appropriate menu item entries
        toggleGroup2.selectToggle(toggleGroup2.getToggles().get(3));
        toggleGroup3.selectToggle(toggleGroup3.getToggles().get(1));

        instance = this; // TODO this is ugly
    }

    /**
     * Handles user input if user clicks "Close" in the file menu
     */
    @FXML
    protected void handleCloseWindow(final ActionEvent e) {
        Platform.exit();
    }

    /**
     * 
     * @param e
     */
    @FXML
    public final void handleOpenProof(ActionEvent e) {
        if (!ComponentFactory.getInstance().hasComponent("treeView")) {
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
                TreeViewController t = ComponentFactory.getInstance().getController("treeView");
                t.loadAndDisplayProof(file);
            }
        }
    }

    /**
     * Handles user input if user clicks "About KeY" in the file menu
     */
    @FXML
    protected void handleAboutWindow(final ActionEvent e) {

    }

    /**
     * Handles user input if the user adds, deletes or moves GUI components by
     * using the file menu
     */
    @FXML
    protected void handleLoadComponent(final ActionEvent e) {
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

    /**
     * @param p
     *            a {@link Place}
     * @return the respective Pane
     * @throws IllegalArgumentException
     *             p == HIDDEN
     */
    protected Pane getPane(final Place p) throws IllegalArgumentException {
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
     * TODO
     * 
     * @param componentName
     *            – the Component to create / relocate / hide
     * @param place
     *            – the place where
     * @param componentResource
     * @throws IllegalArgumentException
     *             The Component componentName already exists in the Place
     *             place.
     */
    public void createOrMoveOrHideComponent(final String componentName, final Place place,
            final String componentResource) throws IllegalArgumentException {
        // Does the component already exist?
        // Then the user wants to either change its place or to hide it
        if (placeComponent.containsKey(componentName)) {
            Node existingcomponent = null;
            for (Node n : getPane(placeComponent.get(componentName)).getChildren()) {
                if (n.getId().equals(componentName)) {
                    existingcomponent = n;
                    break;
                }
            }
            // Add Component to the respective Pane
            // (the list's observer will automatically remove it
            // from the Pane where it currently is listed)
            // and update its position in the posComponent Map.
            if (place == Place.HIDDEN) {
                // for (Node n :
                // getPane(placeComponent.get(componentName)).getChildren()) {
                // if (n.getId().equals(componentName)) {
                // unregisterKeyListener(n.get);
                // }
                // }

                getPane(placeComponent.get(componentName)).getChildren().remove(existingcomponent);
                placeComponent.remove(componentName);
                statustext.setText("View " + componentName + " hidden.");
                ComponentFactory.getInstance().deleteComponent(componentName);
            }
            else {
                getPane(place).getChildren().add(existingcomponent);
                placeComponent.replace(componentName, place);
            }
        }
        else {
            if (place != Place.HIDDEN) {
                // Component did not already exist, thus it must be created
                placeComponent.put(componentName, place);
                Parent newComponent = ComponentFactory.getInstance().createComponent(componentName,
                        componentResource);
                getPane(place).getChildren().add(newComponent);
            }
        }
    }

    /**
     * TODO
     */
    private Map<KeyCode, SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>> keyEventHandlers = new HashMap<>();

    /**
     * TODO
     * 
     * @throws IllegalArgumentException
     *             -- that key is already in use or modifiers does not entirely
     *             consist of modifiers
     */
    public void registerKeyListener(KeyCode k, KeyCode[] modifiers, EventHandler<KeyEvent> e)
            throws IllegalArgumentException {

        if (modifiers != null) {
            for (KeyCode c : modifiers) {
                // blame Java for the fact that I cannot make the compiler do
                // this check
                if (!c.isModifierKey())
                    throw new IllegalArgumentException(
                            "You submitted an illegal modifiers list for the key " + k);
            }
        }
        if (keyEventHandlers.containsKey(k)) {
            // TODO this should better be done when the view is going to be
            // hidden
            // this is just a workaround to make the tests work again
            unregisterKeyListener(k);
            // throw new IllegalArgumentException(
            // "The key you submitted (" + k + ") was already in use.");
        }

        keyEventHandlers.put(k, new SimpleImmutableEntry<EventHandler<KeyEvent>, KeyCode[]>(e,
                (modifiers == null) ? new KeyCode[0] : modifiers));
    }

    /**
     * TODO
     * 
     * @throws IllegalArgumentException
     */
    public void unregisterKeyListener(KeyCode k) throws IllegalArgumentException {
        keyEventHandlers.remove(k);
    }

    /**
     * TODO
     * 
     * @param k
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
}
