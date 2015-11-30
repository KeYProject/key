package de.uka.ilkd.key.nui;

import java.util.HashMap;
import java.util.Map;

import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Controller for the main GUI which is displayed when the program was started
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
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

        MenuItem clickedEntry = (MenuItem) e.getSource();
        Map<Object, Object> m = clickedEntry.getProperties();
        String componentName = (String) m.get("componentName");
        String componentResource = (String) m.get("componentResource");

        // Remove component from pane
        if (posComponent.containsKey(componentName)) {
            Pane pane = posComponent.get(componentName);
            pane.getChildren().removeIf(p -> p.getId().equals(componentName));
        }

        // Determine proper menu button
        MenuButton mb = null;
        switch (componentName) {
        case "proofView":
            mb = ButtonProofView;
            break;
        case "goalView":
            mb = ButtonGoalView;
            break;
        case "openProofsView":
            mb = ButtonOpenProofsView;
            break;
        case "treeView":
            mb = ButtonTreeView;
            break;
        }
        // Update text of menu button
        mb.setText(clickedEntry.getText());

        // Add component to selected pane and update text of menu button
        switch (clickedEntry.getId()) {
        case "toLeft":
            componentFactory.createComponent(componentName, left,
                    componentResource, posComponent);
            break;
        case "toMiddle":
            componentFactory.createComponent(componentName, middle,
                    componentResource, posComponent);
            break;
        case "toRight":
            componentFactory.createComponent(componentName, right,
                    componentResource, posComponent);
            break;
        case "toDown":
            componentFactory.createComponent(componentName, down,
                    componentResource, posComponent);
        default:
            break;
        }
    }
}
