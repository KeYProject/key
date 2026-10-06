/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import javafx.application.Application;
import javafx.application.Platform;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * The JavaFX application of KeY, counter-part of {@code de.uka.ilkd.key.gui.MainWindow} in the
 * Swing module {@code key.ui}.
 * <p>
 * Milestone M0: this is a deliberately minimal, runnable shell. The docking workspace (M1), the
 * menus/toolbars, and the views (M2) replace the placeholder content stage by stage.
 */
public final class MainApplication extends Application {

    @Override
    public void start(final Stage stage) {
        BorderPane root = new BorderPane();

        root.setTop(buildMenuBar());

        Label placeholder = new Label("KeY UI (JavaFX)\n\nThe docking workspace arrives in "
            + "milestone M1.");
        placeholder.setAlignment(Pos.CENTER);
        root.setCenter(placeholder);

        Label statusLine = new Label("Ready");
        BorderPane.setAlignment(statusLine, Pos.CENTER_LEFT);
        root.setBottom(statusLine);

        stage.setTitle("KeY (JavaFX)");
        stage.setScene(new Scene(root, 1024, 768));
        stage.show();
    }

    private MenuBar buildMenuBar() {
        MenuBar menuBar = new MenuBar();

        Menu fileMenu = new Menu("File");
        MenuItem quitItem = new MenuItem("Quit");
        quitItem.setOnAction(e -> Platform.exit());
        fileMenu.getItems().add(new SeparatorMenuItem());
        fileMenu.getItems().add(quitItem);

        menuBar.getMenus().add(fileMenu);
        return menuBar;
    }
}
