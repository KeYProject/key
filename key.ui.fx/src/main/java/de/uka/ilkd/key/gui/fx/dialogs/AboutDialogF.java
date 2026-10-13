/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.Hyperlink;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.help.HelpFacadeF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.util.KeYConstants;

/**
 * The "About KeY" dialog (reviewer request: a real dialog instead of a notification toast).
 * Shows the copyright, the project homepage and the version — the content of the Swing
 * {@code AboutAction.showAbout} message dialog (AboutAction.java:33-39, titled "The KeY
 * Project"), but as a proper modal window with a close button.
 */
public final class AboutDialogF {

    /** Swing {@code AboutAction}: "WWW: http://key-project.org/". */
    private static final String WWW = "http://key-project.org/";

    private AboutDialogF() {
    }

    /**
     * Shows the modal about dialog.
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     */
    public static void show(Window owner) {
        javafx.stage.Stage dialog = new javafx.stage.Stage();
        dialog.setTitle("The KeY Project");
        dialog.initOwner(owner);
        if (owner != null) {
            dialog.initModality(Modality.WINDOW_MODAL);
        }

        Label title = new Label("KeY");
        title.setStyle("-fx-font-size: 26px; -fx-font-weight: bold;");

        Hyperlink www = new Hyperlink(WWW);
        www.setOnAction(e -> HelpFacadeF.openExternal(WWW));

        // Swing AboutAction: the copyright with each "and" on its own line
        Label copyright = new Label(
            KeYConstants.COPYRIGHT.replace("and", "\nand") + "\n\nWWW:");
        copyright.setWrapText(true);
        copyright.getStyleClass().add("about-text");

        // reviewer request: the version must be selectable so it can be copied into bug
        // reports — a read-only borderless text field replaces the label (the about-text look
        // is kept via the style class)
        TextField version = new TextField("Version " + KeYConstants.VERSION);
        version.setEditable(false);
        version.getStyleClass().add("about-text");
        version.setStyle("-fx-background-color: transparent; -fx-padding: 0;");
        version.setPrefColumnCount(version.getText().length());

        VBox center = new VBox(6, title, copyright, www, version);
        center.setPadding(new Insets(16));
        center.setAlignment(Pos.CENTER_LEFT);
        VBox.setVgrow(version, Priority.NEVER);

        Button close = new Button("Close");
        close.setDefaultButton(true);
        ButtonBar.setButtonData(close, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar buttons = new ButtonBar();
        buttons.getButtons().add(close);

        BorderPane root = new BorderPane();
        root.setCenter(center);
        root.setBottom(buttons);
        BorderPane.setMargin(buttons, new Insets(10));
        Scene scene = new Scene(root, 480, 320);
        ThemeManager.getInstance().manage(scene);
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                dialog.close();
                e.consume();
            }
        });
        dialog.setScene(scene);
        close.setOnAction(e -> dialog.close());
        dialog.showAndWait();
    }
}
