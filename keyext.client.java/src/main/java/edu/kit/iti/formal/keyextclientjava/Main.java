/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.keyextclientjava;

import java.io.IOException;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.stage.Stage;

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
