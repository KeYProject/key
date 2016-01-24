package de.uka.ilkd.key.nui;

import java.io.File;
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
public final class ComponentFactory {

	/**
	 * Directory for FXML files.
	 */
	private static String resourceDir;

	/**
	 * Singleton.
	 */
	private static ComponentFactory instance;

	/**
	 * Returns the singleton instance of the ComponentFactory.
	 * 
	 * @return the single instance of <tt>this</tt>
	 */
	public static ComponentFactory getInstance() {
		if (instance == null) {
			instance = new ComponentFactory();
		}
		return instance;
	}

	/**
	 * Singleton constructor.
	 */
	private ComponentFactory() {

	}
	
	/**
	 * A HashMap storing the components created by <tt>this</tt>, or to be more
	 * precise, it stores the Parent to provide references to the actual
	 * components and the FXMLLoader to provide references to the respective
	 * Controllers.
	 */
	private final Map<String, ComponentMapEntry> componentMap = new HashMap<>();
	
	/**
	 * This class encapsulates a
	 * <tt>java.util.AbstractMap.SimpleImmutableEntry<FXMLLoader, Parent></tt>
	 * to make the ComponentFactory more readable.
	 * 
	 * @author Stefan Pilot
	 *
	 */
	private class ComponentMapEntry {
		/**
		 * An immutable entry mapping FXMLoaders to Nodes.
		 */
		private final SimpleImmutableEntry<FXMLLoader, Parent> entry;

		/**
		 * Creates a new ComponentMapEntry consisting of a FXMLLoader loader and a Parent parent.
		 * 
		 * @param loader
		 * 			The FXMLLoader.
		 * @param parent
		 * 			The Parent corresponding to the FXMLLoader.
		 */
		ComponentMapEntry(final FXMLLoader loader, final Parent parent) {
			entry = new SimpleImmutableEntry<>(loader, parent);
		}

		/**
		 * Returns the controller corresponding to the FXMLLoader.
		 * 
		 * @return the controller.
		 */
		public <T> T getController() {
			return entry.getKey().getController();
		}

		/**
		 * Returns the component corresponding to the controller.
		 * 
		 * @return the corresponding component.
		 */
		public Parent getComponent() {
			return entry.getValue();
		}
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
	public Parent createComponent(final String id, final String resource) {
		Parent component = null;
		try {
			final FXMLLoader loader = new FXMLLoader(getClass().getResource(ComponentFactory.resourceDir + resource));
			component = loader.load();
			component.setId(id);
			componentMap.put(id, new ComponentMapEntry(loader, component));
		} catch (IOException e) {
			e.printStackTrace();
		}
		return component;
	}

	/**
	 * Deletes all references to a certain component stored by <tt>this</tt>.
	 * 
	 * @param id
	 *            The Components FXID or another identifier specified at
	 *            construction.
	 */
	public void deleteComponent(final String id) {
		componentMap.remove(id);
	}

	/**
	 * Checks whether a certain component is currently being stored.
	 * 
	 * @param id
	 *            The Components FXID or another identifier specified at
	 *            construction.
	 * @return boolean
	 * 				True iff the component is already stored.
	 * 
	 */
	public boolean hasComponent(final String id) {
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
	public Parent getComponent(final String id) {
		return componentMap.get(id).getComponent();
	}

	/**
	 * Returns a controller for a given component specified by their FXID.
	 * 
	 * @param id
	 *            The Components FXID or another identifier specified at
	 *            construction.
	 * 
	 * @return the Controller, or <tt> null </tt>, if no component with this ID is
	 *         currently stored
	 */
	public <T> T getController(final String id) {
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
		ResourceBundle bundle = null;
		Parent root = null;
		try {
			// Load the default bundle
			bundle = new PropertyResourceBundle(getClass().getResourceAsStream("bundle_en_EN.properties"));
			// Load FXML from main window
			final FXMLLoader loader = new FXMLLoader(getClass().getResource("NUIdefault.fxml"), bundle);
			root = loader.load();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return root;
	}
	
	/**
	 * Set the resource directory containing the FXML files, e.g. "components/".
	 * 
	 * @param resourceDir
	 * 			The relative path to the resource directory with the FXML files.
	 */
	public static void setResourceDirectory(final String resourceDir) {
		if (!(resourceDir.endsWith(File.separator))) {
			ComponentFactory.resourceDir = resourceDir + File.separator;
		} else {
			ComponentFactory.resourceDir = resourceDir;
		}
	}
}
