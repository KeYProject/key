package de.uka.ilkd.key.nui.controller;

import java.net.URL;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;
import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.application.Platform;
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
    private HashMap<String, Place> placeComponent = new HashMap<>();

    /**
     * Factory to create GUI components
     */
    private ComponentFactory componentFactory = new ComponentFactory("components/");

    /**
     * TODO
     * 
     */
    public enum Place {
        LEFT, MIDDLE, RIGHT, BOTTOM, HIDDEN
    }
    
    /**
     * TODO
     */
    private static NUIController instance; // TODO this is ugly
    
    /**
     * TODO
     * @return
     */
    public static NUIController getInstance() {
        return instance; // TODO this is ugly
    }

    /**
     * @return the placeComponent
     */
    public HashMap<String, Place> getPlaceComponent() {
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
    public void initialize(URL location, ResourceBundle resources) {
        // Load default components
        createComponent("treeView", Place.LEFT, "treeView.fxml");
        createComponent("proofView", Place.RIGHT, "proofView.fxml");
        // Select appropriate menu item entries
        toggleGroup2.selectToggle(toggleGroup2.getToggles().get(3));
        toggleGroup3.selectToggle(toggleGroup3.getToggles().get(1));

        instance = this; // TODO this is ugly
    }

    /**
     * Handles user input if user clicks "Close" in the file menu
     */
    @FXML
    protected void handleCloseWindow(ActionEvent e) {
        Platform.exit();
    }

    /**
     * Handles user input if user clicks "About KeY" in the file menu
     */
    @FXML
    protected void handleAboutWindow(ActionEvent e) {

    }

    /**
     * Handles user input if the user adds, deletes or moves GUI components by
     * using the file menu
     */
    @FXML
    protected void handleLoadComponent(ActionEvent e) {
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

        createComponent(componentName, place, componentResource);
    }

    /**
     * @param p
     *            a {@link Place}
     * @return the respective Pane
     * @throws IllegalArgumentException
     *             p == HIDDEN
     */
    protected Pane getPane(Place p) {
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
     * @param place
     * @param componentResource
     * @throws IllegalArgumentException
     *             The Component componentName already exists in the Place
     *             place.
     */
    public void createComponent(String componentName, Place place, String componentResource)
            throws IllegalArgumentException {
        // Does the component already exist?
        // Then the user wants either to change its place or to hide it
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
                getPane(placeComponent.get(componentName)).getChildren().remove(existingcomponent);
                placeComponent.remove(componentName);
                statustext.setText("View " + componentName + " hidden.");
            }
            else {
                getPane(place).getChildren().add(existingcomponent);
                placeComponent.replace(componentName, place);
            }

        }
        else { // Component did not already exist, thus it must be created
            placeComponent.put(componentName, place);
            Parent newComponent = componentFactory
                    .createComponent(componentName, componentResource);
            getPane(place).getChildren().add(newComponent);
        }
    }

    /**
     * TODO
     * 
     * @param k
     */
    public void handleKeyPressed(KeyEvent k) {
        switch (k.getCode()) {
        case ESCAPE:
            createComponent(".searchView", Place.HIDDEN, ".searchView.fxml");
            break;
        case F:
            if (k.isControlDown() && placeComponent.containsKey("treeView")) {
                Place p = placeComponent.get("treeView");

                try {
                    createComponent(".searchView", p, ".searchView.fxml");
                }
                catch (IllegalArgumentException ex) {
                    // SearchView already exists
                    SearchViewController.getInstance().SearchTextField.requestFocus();
                    // TODO this is the ugliest solution possible
                }
            }
            break;
        default:
            break;
        }
    }
}
