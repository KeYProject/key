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

    /**
     * Singleton.
     */
	private static ComponentFactory instance;

    /**
     * Singleton.
     * 
     * @return the single instance of <tt>this</tt>
     */
	public static ComponentFactory getInstance() {
		if (instance == null) {
			instance = new ComponentFactory();
			return instance;
        }
        else {
			return instance;
		}
	}

    /**
     * Singleton constructor.
     */
	private ComponentFactory() {

	}

	/**
     * This class encapsulates a
     * java.util.AbstractMap.SimpleImmutableEntry<FXMLLoader, Parent> just to
     * make the ComponentFactory more readable.
	 * 
	 * @author Stefan Pilot
	 *
	 */
	private class ComponentMapEntry {
		private SimpleImmutableEntry<FXMLLoader, Parent> e;

		public ComponentMapEntry(FXMLLoader l, Parent p) {
			e = new SimpleImmutableEntry<>(l, p);
		}

		public <T> T getController() {
			return e.getKey().getController();
		}

		public Parent getComponent() {
			return e.getValue();
		}
	}

    /**
     * A HashMap storing the components created by <tt>this</tt>, or to be more
     * precise, it stores the Parent to provide references to the actual
     * components and the FXMLLoader to provide references to the respective
     * Controllers.
     */
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
            FXMLLoader loader = new FXMLLoader(
                    getClass().getResource(ComponentFactory.resourceDir + resource));
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
     * Deletes all references to a certain component stored by <tt>this</tt>
	 * 
	 * @param id
     *            The Components FXID or another identifier specified at
     *            construction.
	 */
	public void deleteComponent(String id) {
		componentMap.remove(id);
	}

	/**
     * Checks whether a certain component is currently being stored.
	 * 
	 * @param id
     *            The Components FXID or another identifier specified at
     *            construction.
	 */
	public boolean hasComponent(String id) {
		return componentMap.containsKey(id);
	}

	/**
     * Returns a reference to a certain NUI Component.
	 * 
	 * @param id
     *            The Components FXID or another identifier specified at
     *            construction.
     * @return A reference.
	 */
	public Parent getComponent(String id) {
		return componentMap.get(id).getComponent();
	}

	/**
     * Returns a controller for a given component specified by their FXID.<br/>
	 * 
	 * @param id
     *            The Components FXID or another identifier specified at
     *            construction.
	 * 
     * @return the Controller, or <t> null </t>, if no component with this ID is
     *         currently stored
	 */
	public <T> T getController(String id) {
		if (hasComponent(id)) {
			return componentMap.get(id).getController();
		}
		return null;
	}

	/**
     * Creates and returns the JavaFX scenegraph for the application window.
	 * 
	 * @return returns the JavaFX scenegraph for the application window
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

    // TODO what is this? eliminate or document.
	public static void setInstance(String resourceDir) {
		ComponentFactory.resourceDir = resourceDir;
	}
}
