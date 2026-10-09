/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.util.List;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.stage.Stage;
import javafx.stage.Window;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Small dialog showing the Isabelle translations of the context-menu actions, FX port of the
 * Swing {@code org.key_project.isabelletranslation.gui.InformationWindow}
 * (InformationWindow.java:27-98): one tab per translated goal with the generated theory text.
 */
@NullMarked
final class IsabelleTranslationDialogF {

    /**
     * One translation result: the preamble and the translation theory of a goal, or the exception
     * message of a failed translation.
     */
    record Entry(String name, @Nullable String preamble, @Nullable String translation,
            @Nullable String error) {

        /** The tab title of this entry (Swing IsabelleProblem.getName: "Goal <serialNr>"). */
        String title() {
            return error == null ? name : name + " (failed)";
        }

        /** The text shown in the tab. */
        String content() {
            if (error != null) {
                return "Translation failed:\n" + error;
            }
            StringBuilder sb = new StringBuilder();
            if (preamble != null) {
                sb.append(preamble).append(System.lineSeparator()).append(System.lineSeparator());
            }
            if (translation != null) {
                sb.append(translation);
            }
            return sb.toString();
        }
    }

    private IsabelleTranslationDialogF() {
    }

    /**
     * Shows the translations of all goals in a modal dialog.
     *
     * @param owner the owner window, may be {@code null}
     * @param entries the translation entries (one per goal), non-null
     */
    static void show(@Nullable Window owner, List<Entry> entries) {
        if (entries == null || entries.isEmpty()) {
            Alert alert = new Alert(Alert.AlertType.INFORMATION, "No translations to show.");
            alert.setTitle("Isabelle Translation");
            if (owner != null) {
                alert.initOwner(owner);
            }
            alert.showAndWait();
            return;
        }
        // extension: MP9.3 — Swing InformationWindow.java:33-46: a tab pane with one tab per
        // translation; the read-only text areas mirror the JTextArea content plus the row-header
        // line numbers (the line numbers are a pure cosmetic detail and are omitted here).
        Stage stage = new Stage();
        if (owner != null) {
            stage.initOwner(owner);
        }
        stage.setTitle("Isabelle Translation");
        TabPane tabPane = new TabPane();
        for (Entry entry : entries) {
            TextArea area = new TextArea(entry.content());
            area.setEditable(false);
            area.setWrapText(true);
            area.setPrefSize(600, 480);
            Tab tab = new Tab(entry.title(), area);
            tab.setClosable(false);
            tabPane.getTabs().add(tab);
        }
        stage.setScene(new Scene(tabPane, 640, 520));
        stage.show();
    }
}
