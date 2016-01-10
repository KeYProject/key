package de.uka.ilkd.key.nui;

import java.io.File;
import java.util.Arrays;

import javafx.application.Application;
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
    
    public static File initialProofFile;
    
    public static void main(String[] args) {
        if(args.length != 0)
            initialProofFile = new File(System.getProperty("user.dir") + args[0]);
        launch(args);
    }
    
    /**
     * When program is starting method "start" is called
     */
    @Override
    public void start(Stage stage) throws Exception {
        ComponentFactory.setInstance("components/");
        Parent root = ComponentFactory.getInstance().createNUISceneGraph();

        // Load scene and set preferences
        Scene scene = new Scene(root);
        stage.setTitle("KeY");
        stage.setScene(scene);
        stage.show();
    }
}
