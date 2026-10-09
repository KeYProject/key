/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.drawer;

import javafx.collections.ListChangeListener;
import javafx.scene.Node;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * The content area of a {@link DrawerF}: a {@link VBox} hosting the content of every currently
 * expanded item. Expanded items share the available space equally (each child gets
 * {@link Priority#ALWAYS} vertical growth), which is the "split pane" behaviour of the TornadoFX
 * original (TornadoFX {@code ExpandedDrawerContentArea}).
 *
 * @see DrawerF
 */
public class DrawerContentAreaF extends VBox {

    public DrawerContentAreaF() {
        setStyle("-fx-border-color: darkgray; -fx-border-width: 0.5;");
        getChildren().addListener((ListChangeListener<Node>) change -> {
            while (change.next()) {
                if (change.wasAdded()) {
                    for (Node added : change.getAddedSubList()) {
                        if (VBox.getVgrow(added) == null) {
                            VBox.setVgrow(added, Priority.ALWAYS);
                        }
                    }
                }
            }
        });
    }
}
