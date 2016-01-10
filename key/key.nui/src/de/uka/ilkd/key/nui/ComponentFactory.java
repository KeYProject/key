package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.Map;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;

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
    private static String resourceDir;

    private static ComponentFactory instance;

    public static ComponentFactory getInstance() {
        if (instance == null) {
            instance = new ComponentFactory();
            return instance;
        }
        else {
            return instance;
        }
    }

    private ComponentFactory() {
        
    }

    /**
     * 
     * @author Stefan Pilot
     *
     */
    private class ComponentMapEntry {
        /**
         * 
         */
        private SimpleImmutableEntry<FXMLLoader, Parent> e;

        /**
         * 
         * @param l
         * @param p
         */
        public ComponentMapEntry(FXMLLoader l, Parent p) {
            e = new SimpleImmutableEntry<>(l, p);
        }

        /**
         * 
         * @return
         */
        public <T> T getController() {
            return e.getKey().getController();
        }

        /**
         * 
         * @return
         */
        public Parent getComponent() {
            return e.getValue();
        }
    }

    private Map<String, ComponentMapEntry> componentMap = new HashMap<>();

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
            FXMLLoader loader = new FXMLLoader(getClass().getResource(this.resourceDir + resource));
            component = loader.load();
            component.setId(id);
            componentMap.put(id, new ComponentMapEntry(loader, component));
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        return component;
    }

    /**
     * 
     * @param id
     */
    public void deleteComponent(String id) {
        componentMap.remove(id);
    }

    /**
     * 
     * @param id
     */
    public boolean hasComponent(String id) {
        return componentMap.containsKey(id);
    }

    /**
     * 
     * @param id
     * @return
     */
    public Parent getComponent(String id) {
        return componentMap.get(id).getComponent();
    }

    /**
     * Returns a controller for a given component specified by ID.<br/>
     * 
     * @param id
     *            the Components ID
     * 
     * @return the Controller, or <t> null </t>, if a component with this ID is
     *         not currently stored
     */
    public <T> T getController(String id) {
        if (hasComponent(id)) {
            return componentMap.get(id).getController();
        }
        return null;
    }

    /**
     * Creates and returns the JavaFX scenegraph for the application window TODO
     * this tends to return null sometimes. But when exactly?
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
            e.printStackTrace();
        }

        // Load FXML from main window
        FXMLLoader loader = new FXMLLoader(getClass().getResource("NUIdefault.fxml"), bundle);

        Parent root = null;

        try {
            root = loader.load();
        }
        catch (IOException e) {
            e.printStackTrace();
        }

        return root;
    }

    public static void setInstance(String resourceDir) {
        ComponentFactory.resourceDir = resourceDir;
    }
}
