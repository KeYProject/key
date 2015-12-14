package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.util.HashMap;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.layout.Pane;

/**
 * Factory for creating GUI components.
 * 
 * @author Florian Breitfelder
 * @author Stefan Pilot
 *
 */
public class ComponentFactory {

    /**
     * directory for fxml files
     */
    private String resourceDir;

    public ComponentFactory(String resourceDir) {
        this.resourceDir = resourceDir;
    }

    /**
     * Creates a new GUI component and places it in the given pane
     * 
     * @param id
     *            identifier for the new GUI component
     * @param pane
     *            here the new GUI component is placed
     * @param resource
     *            name of the fxml file for the new GUI component
     * @param posComponent
     *            here the position of the new GUI component is stored e. g.
     *            left, right, etc.
     * @return a new type Parent GUI component e. g. treeView
     */
    public Parent createComponent(String id, Pane pane, String resource,
            HashMap<String, Pane> posComponent) {
        Parent component = null;
        try {
            component = FXMLLoader
                    .load(getClass().getResource(this.resourceDir + resource));
            component.setId(id);
            posComponent.put(id, pane);
            pane.getChildren().add(component);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        return component;
    }
    
    /**
     * Returns a new GUI component. Caller is left with placing it in the
     * correct pane.
     * 
     * @param id
     *            identifier for the new GUI component
     * @param resource
     *            name of the fxml file for the new GUI component
     * @return a new type Parent GUI component e. g. treeView
     * 
     */
    public Parent createComponent(String id, String resource) {
        Parent component = null;
        try {
            component = FXMLLoader
                    .load(getClass().getResource(this.resourceDir + resource));
            component.setId(id);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        return component;
    }

    /**
     * Creates and returns the JavaFX scenegraph for the application window
     * 
     * @return returns the JavaFX scenegraph for the application window
     * @throws Exception
     */
    public Parent createNUISceneGraph() {
        // Set default language bundle
        ResourceBundle bundle = null;

        try {
            bundle = new PropertyResourceBundle(
                    getClass().getResourceAsStream("bundle_en_EN.properties"));
        }
        catch (IOException e) {
        }

        // Load FXML from main window
        FXMLLoader loader = new FXMLLoader(
                getClass().getResource("NUIdefault.fxml"), bundle);

        Parent root = null;

        try {
            root = loader.load();
        }
        catch (IOException e) {
        }

        return root;
    }

    public Parent createTreeView() {
        Parent treeView = null;
        try {
            treeView = FXMLLoader.load(getClass().getResource(
                    "components/treeView.fxml"));
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
        }
        return treeView;
    }

    
}
