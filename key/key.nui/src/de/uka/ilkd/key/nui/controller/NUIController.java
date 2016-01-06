package de.uka.ilkd.key.nui.controller;

import java.net.URL;
import java.util.HashMap;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.application.Platform;
import javafx.event.ActionEvent;
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

/**
 * Controller for the main GUI which is displayed when the program was started
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 *
 */
public class NUIController implements Initializable{

    /**
     * Stores the position of components added to the SplitPane
     */
    private HashMap<String, Pane> posComponent = new HashMap<String, Pane>();

    /**
     * Factory to create GUI components
     */
    private ComponentFactory componentFactory = new ComponentFactory(
            "components/");
    /**
     * TODO
     * 
     */
    public enum Place{
        LEFT,
        MIDDLE,
        RIGHT,
        BOTTOM,
        HIDDEN
    }
    
    private static NUIController instance; // TODO this is ugly
    
    public static NUIController getInstance() {
        return instance; // TODO this is ugly
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
        createComponent("treeView", left, "treeView.fxml");
        createComponent("proofView", right, "proofView.fxml");
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
     * Creates a component (yay for low coupling!) TODO expand this javadoc
     */
    protected void createComponent(String id, Pane location, String resource) {
        posComponent.put(id, location);
        Parent newComponent = componentFactory.createComponent(id, resource);
        location.getChildren().add(newComponent);
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
            place = Place.LEFT; break;
        case "middle":
            place = Place.MIDDLE; break;
        case "right":
            place = Place.RIGHT; break;
        case "bottom":
            place = Place.BOTTOM; break;
        default: 
            place = Place.HIDDEN; break;
        }

        String componentResource = (String) clickedItem.getParentMenu()
                .getProperties().get("componentResource");
        
        createComponent(componentName, place, componentResource);
    }
    
    /**
     * TODO
     * @param componentName
     * @param place
     * @param componentResource
     */
    public void createComponent(String componentName, Place place, String componentResource){
        // Does the component already exist?
        // Then the user wants either to change change its place or to hide it
        if (posComponent.containsKey(componentName)) {

            Node existingcomponent = null;
            for (Node n : posComponent.get(componentName).getChildren()) {
                if (n.getId().equals(componentName)) {
                    existingcomponent = n;
                    break;
                }
            }

            switch (place) {
            // where to does the User want to move the component?
            // Add Component to the respective Pane
            // (the list's observer will automatically remove it
            // from the Pane where it currently is listed)
            // and update its position in the posComponent Map.
            case LEFT:
                left.getChildren().add(existingcomponent);
                posComponent.replace(componentName, left);
                break;

            case MIDDLE:
                middle.getChildren().add(existingcomponent);
                posComponent.replace(componentName, middle);
                break;

            case RIGHT:
                right.getChildren().add(existingcomponent);
                posComponent.replace(componentName, right);
                break;

            case BOTTOM:
                bottom.getChildren().add(existingcomponent);
                posComponent.replace(componentName, bottom);
                break;

            default: // hide was chosen, delete component and remove it from the
                     // map
                posComponent.get(componentName).getChildren()
                        .remove(existingcomponent);
                posComponent.remove(componentName);
                statustext.setText("View " + componentName + " hidden.");
            }

        }
        else { // Component did not already exist, thus it must be created
            switch (place) {
            // where to does the User want to move the component?
            case LEFT:
                createComponent(componentName, left, componentResource);
                break;
            case MIDDLE:
                createComponent(componentName, middle, componentResource);
                break;
            case RIGHT:
                createComponent(componentName, right, componentResource);
                break;
            case BOTTOM:
                createComponent(componentName, bottom, componentResource);
            default:
                break;
            }
        }
    }
}