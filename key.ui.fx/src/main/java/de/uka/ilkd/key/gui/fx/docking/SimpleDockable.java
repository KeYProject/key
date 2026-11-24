/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.util.Objects;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.scene.Node;

/**
 * Straightforward implementation of a {@link Dockable} with plain JavaFX properties.
 * <p>
 * Most views (proof tree, sequent, source view, ...) are wrapped in a {@code SimpleDockable}
 * before being opened in the {@link DockWorkspace}.
 */
public class SimpleDockable implements Dockable {

    private final String id;
    private final StringProperty title = new SimpleStringProperty(this, "title");
    private final ObjectProperty<Node> content = new SimpleObjectProperty<>(this, "content");
    private final ObjectProperty<Node> icon = new SimpleObjectProperty<>(this, "icon");
    private final BooleanProperty closable = new SimpleBooleanProperty(this, "closable", true);

    /**
     * Creates a closable dockable without an icon.
     *
     * @param id unique identifier used for layout persistence
     * @param title initial title
     * @param content the content node
     */
    public SimpleDockable(String id, String title, Node content) {
        this(id, title, content, null);
    }

    /**
     * Creates a closable dockable.
     *
     * @param id unique identifier used for layout persistence
     * @param title initial title
     * @param content the content node
     * @param icon optional icon shown in the tab header (may be {@code null})
     */
    public SimpleDockable(String id, String title, Node content, Node icon) {
        this.id = Objects.requireNonNull(id, "id");
        this.title.set(title);
        this.content.set(content);
        this.icon.set(icon);
    }

    @Override
    public String getId() {
        return id;
    }

    @Override
    public StringProperty titleProperty() {
        return title;
    }

    @Override
    public ObjectProperty<Node> contentProperty() {
        return content;
    }

    @Override
    public ObjectProperty<Node> iconProperty() {
        return icon;
    }

    @Override
    public BooleanProperty closableProperty() {
        return closable;
    }
}
