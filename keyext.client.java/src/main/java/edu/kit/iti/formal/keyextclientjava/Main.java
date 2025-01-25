package edu.kit.iti.formal.keyextclientjava;

import javafx.application.Application;
import javafx.geometry.Orientation;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular;
import org.kordamp.ikonli.javafx.FontIcon;

import java.io.IOException;
import java.util.concurrent.ForkJoinPool;

public class Main {
    public static class HelloApplication extends Application {
        @Override
        public void start(Stage stage) throws IOException {
            Scene scene = new Scene(new MyKeyClient().root, 320, 240);
            stage.setTitle("KeY Demo");
            stage.setScene(scene);
            stage.show();
        }

    }
    public static void main(String[] args) {
        Application.launch(HelloApplication.class, args);
    }
}