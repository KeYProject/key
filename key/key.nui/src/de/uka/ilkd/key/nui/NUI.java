package de.uka.ilkd.key.nui;

import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

/**
 * Main Class for initializing the GUI
 * 
 * @author Florian Breitfelder
 *
 */
public class NUI extends Application {

    public static void main(String[] args) {
        launch(args);
    }

    /**
     * When program is starting method "start" is called
     */
    @Override
    public void start(Stage stage) throws Exception {
        ComponentFactory factory = new ComponentFactory("");

        Parent root = factory.createNUISceneGraph();

        // Load scene and set preferences
        Scene scene = new Scene(root);
        stage.setTitle("KeY");
        stage.setScene(scene);
        stage.show();
    }
}
