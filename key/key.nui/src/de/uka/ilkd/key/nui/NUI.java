package de.uka.ilkd.key.nui;

import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

public class NUI extends Application {

	public static void main(String[] args) {
		launch(args);
	}

	@Override
	public void start(Stage stage) throws Exception {
		// Set default language bundle
		ResourceBundle bundle = new PropertyResourceBundle(getClass().getResourceAsStream("bundle_en_EN.properties"));
		// Load FXML from main window
		FXMLLoader loader = new FXMLLoader(getClass().getResource("NUIdefault.fxml"), bundle);

		Parent root = loader.load();
		
		Scene scene = new Scene(root);
		stage.setTitle("KeY");
		stage.setScene(scene);
		stage.show();

	}

}
