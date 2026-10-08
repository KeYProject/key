/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.util.List;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.scene.Node;

/**
 * A dockable unit of the JavaFX UI: a titled, optionally closable piece of {@link Node} content
 * that can be placed into a dock role area of the {@link DockWorkspace}.
 * <p>
 * Counter-part of a Docking Frames {@code Dockable} in the Swing module {@code key.ui}. The
 * title, icon, content and closability are exposed as JavaFX properties so that the tab
 * presentation stays in sync when a view updates its title or icon.
 */
public interface Dockable {

    /**
     * @return an identifier that is unique within a {@link DockWorkspace}; used for layout
     *         persistence
     */
    String getId();

    /**
     * @return the title of this dockable (bound to the tab label)
     */
    StringProperty titleProperty();

    /**
     * @return the current title
     */
    default String getTitle() {
        return titleProperty().get();
    }

    /**
     * Sets the title.
     *
     * @param title the new title
     */
    default void setTitle(String title) {
        titleProperty().set(title);
    }

    /**
     * @return the content shown when this dockable is open
     */
    ObjectProperty<Node> contentProperty();

    /**
     * @return the content shown when this dockable is open
     */
    default Node getContent() {
        return contentProperty().get();
    }

    /**
     * @return an optional icon node shown in the tab header (may be {@code null})
     */
    ObjectProperty<Node> iconProperty();

    /**
     * @return the icon shown in the tab header, or {@code null} if none
     */
    default Node getIcon() {
        return iconProperty().get();
    }

    /**
     * @return whether the user may close this dockable (tab close button)
     */
    BooleanProperty closableProperty();

    /**
     * @return whether the user may close this dockable
     */
    default boolean isClosable() {
        return closableProperty().get();
    }

    /**
     * Sets whether the user may close this dockable.
     *
     * @param closable {@code true} to make it closable
     */
    default void setClosable(boolean closable) {
        closableProperty().set(closable);
    }

    /**
     * @return the custom actions shown in this dockable's tab context menu (and later in its tab
     *         header), like the Swing {@code TabPanel.getTitleActions()}/{@code
     *         TabPanel.getTitleCActions()} rendered by {@code DockingHelper} into the dockable's
     *         title bar and title popup menu
     */
    default List<DockTitleActionF> getTitleActions() {
        return List.of();
    }
}
