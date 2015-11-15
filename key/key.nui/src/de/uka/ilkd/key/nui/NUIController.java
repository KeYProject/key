package de.uka.ilkd.key.nui;

import java.util.HashMap;
import java.util.Map;

import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.control.Button;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.input.ContextMenuEvent;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

public class NUIController {

    // Used to determine where component should be placed on
    private Pane lastClicked;

    // Stores the position of components added to the SplitPane
    private HashMap<String, Pane> posComponent = new HashMap<String, Pane>();

    private ComponentFactory componentFactory = new ComponentFactory(
            "components/");

    // Definition of GUI fields
    @FXML
    VBox left;
    @FXML
    AnchorPane middle;
    @FXML
    VBox right;
    @FXML
    Parent root;
    @FXML
    Label statustext;
    @FXML
    ContextMenu contextMenu;
    @FXML
    MenuButton ButtonProof;
    @FXML
    MenuButton ButtonGoals;
    @FXML
    MenuButton ButtonUserConstraint;
    @FXML
    MenuButton ButtonProofSearchStrategy;
    @FXML
    MenuButton ButtonRules;

    @FXML
    protected void handleCloseWindow(ActionEvent e) {
        Platform.exit();
    }

    @FXML
    protected void handleAboutWindow(ActionEvent e) {
        System.out.println("Clicked 'About'.");
    }
    

    @FXML
    protected void handleLoadComponent(ActionEvent e) {
        
        MenuItem clickedEntry = (MenuItem) e.getSource();
        Map<Object, Object> m = clickedEntry.getProperties();    
        String componentName = (String) m.get("componentName");
    
        // Remove component from pane
        if (posComponent.containsKey(componentName)) {
            Pane pane = posComponent.get(componentName);
            pane.getChildren().removeIf(p -> p.getId().equals(componentName));
        }
        
        // Determine proper menu button
        MenuButton mb = null;
        switch (componentName) {
        case "proof":
            mb = ButtonProof;
            break;
        case "goals":
            mb = ButtonGoals;
            break;
        case "userConstraint":
            mb = ButtonUserConstraint;
            break;
        case "proofSearchStrategy":
            mb = ButtonProofSearchStrategy;
            break;
        case "rules":
            mb = ButtonRules;
            break;
        }
        // Update text of menu button
        mb.setText(clickedEntry.getText());
        
        // Add component to selected pane and update text of menu button
        switch (clickedEntry.getId()) {
        case "toLeft":
            componentFactory.createTreeView(componentName, left, posComponent);
            break;
        case "toMiddle":
            componentFactory.createTreeView(componentName, middle, posComponent);
            break;
        case "toRight":
            componentFactory.createTreeView(componentName, right, posComponent);
            break;
        default:
            break;
        }
    }
    
    @FXML
    protected void handleLoadGoals(ActionEvent e) {
    }

    @FXML
    protected void handleLoadUserConstraint(ActionEvent e) {
    }

    @FXML
    protected void handleLoadProofSearchStrategy(ActionEvent e) {
    }

    @FXML
    protected void handleLoadRules(ActionEvent e) {
    }

    /**
     * Initialization method for scene
     */
    public void initialize() {
    }
}
