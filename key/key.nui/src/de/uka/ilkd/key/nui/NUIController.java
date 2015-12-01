package de.uka.ilkd.key.nui;

import java.util.HashMap;
import java.util.Map;

import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuButton;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.scene.control.RadioMenuItem;

/**
 * Controller for the main GUI which is displayed when the program was started
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 * @author Stefan Pilot
 *
 */
public class NUIController {

    // Stores the position of components added to the SplitPane
    private HashMap<String, Pane> posComponent = new HashMap<String, Pane>();

    // Factory to create GUI components
    private ComponentFactory componentFactory = new ComponentFactory(
            "components/");

    // Definition of GUI fields
    @FXML
    VBox left;
    @FXML
    VBox middle;
    @FXML
    VBox right;
    @FXML
    HBox down;
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
        Map<Object, Object> m = clickedItem.getParentMenu().getProperties();
        String componentName = (String) m.get("componentName");
        String componentResource = (String) m.get("componentResource");
  
        // Does the component already exist? Then just change its place
        if (posComponent.containsKey(componentName)) {
            Node existingcomponent = null;
            for(Node n : posComponent.get(componentName).getChildren()){
                if(n.getId().equals(componentName)) existingcomponent = n; break;
            }
            switch(clickedItem.getText()) {
            case "left":     left.getChildren().add(existingcomponent); posComponent.replace(componentName, left); break;
            case "middle": middle.getChildren().add(existingcomponent); posComponent.replace(componentName, middle); break;
            case "right":   right.getChildren().add(existingcomponent); posComponent.replace(componentName, right); break;
            case "bottom":   down.getChildren().add(existingcomponent); posComponent.replace(componentName, down); break;
            default: /* hide was chosen */ 
                posComponent.get(componentName).getChildren().remove(existingcomponent);
                posComponent.remove(componentName);
                statustext.setText("View " + componentName + " hidden.");
            }
            
        } else // Component did not already exist, thus it must be created
        
        switch(clickedItem.getText()) {
        case "left":
            componentFactory.createComponent(componentName, left,
                    componentResource, posComponent);
            break;
        case "middle":
            componentFactory.createComponent(componentName, middle,
                    componentResource, posComponent);
            break;
        case "right":
            componentFactory.createComponent(componentName, right,
                    componentResource, posComponent);
            break;
        case "down":
            componentFactory.createComponent(componentName, down,
                    componentResource, posComponent);
        default:
            break; 
        }
    }
}
