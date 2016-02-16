package de.uka.ilkd.key.nui;

import java.io.File;

import javafx.application.Application;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

/**
 * Main Class for initializing the GUI.
 * 
 * @author Florian Breitfelder
 *
 */
public class NUI extends Application {

	/**
	 * The proof file initially (at program startup) loaded.
	 */
	private static File initialProofFile;

	/**
	 * The main method.
	 * 
	 * @param args
	 *            The arguments passed to the program.
	 */
	public static void main(final String... args) {
		if (args.length != 0) {
			initialProofFile = new File(System.getProperty("user.dir") + args[0]);
		}
		launch(args);
	}

	/**
	 * When program is starting method "start" is called.
	 */
	@Override
	public final void start(final Stage stage) {
		ComponentFactory.setResourceDirectory("components/");
		final Parent root = ComponentFactory.getInstance().createNUISceneGraph();
		

		// Load scene and set preferences
		final Scene scene = new Scene(root);
		stage.setTitle("KeY");
		stage.setScene(scene);
		stage.show();
	}

	/**
	 * Returns the proof file initially loaded.
	 * 
	 * @return initialProofFile the proof file initially loaded
	 */
	public static File getInitialProofFile() {
		return initialProofFile;
	}
}
