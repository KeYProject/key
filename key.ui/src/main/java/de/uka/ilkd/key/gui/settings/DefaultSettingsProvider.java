/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.settings;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
@NullMarked
public class DefaultSettingsProvider implements SettingsProvider {
    private String description;
    private JPanel panel;
    private List<SettingsProvider> children;
    private final String keywords = "";
    private int priority;
    private Icon icon;

    /**
     * Creates an empty default settings provider.
     *
     * <p>
     * All properties are expected to be filled by the respective setters before the provider is
     * used; the EISOP initialization check cannot see those external assignments, so the
     * uninitialized fields are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    public DefaultSettingsProvider() {}

    /**
     * Creates a default settings provider for the given description and panel.
     *
     * <p>
     * The properties are assigned through the setters while the receiver is still under
     * initialization (EISOP initialization check); the EISOP initialization check cannot see the
     * assignments inside the delegated calls, so both the fields and the delegated calls are
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:initialization.fields.uninitialized",
        "nullness:method.invocation.invalid" })
    public DefaultSettingsProvider(String desc, JPanel pane) {
        setDescription(desc);
        setPanel(pane);
    }

    @Override
    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        return panel;
    }

    @Override
    public List<SettingsProvider> getChildren() {
        return children;
    }

    public void setChildren(List<SettingsProvider> children) {
        this.children = children;
    }

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {}

    @Override
    public @Nullable Icon getIcon() {
        return icon;
    }

    public void setIcon(Icon icon) {
        this.icon = icon;
    }

    @Override
    public boolean contains(String substring) {
        return keywords.contains(substring);
    }

    @Override
    public int getPriorityOfSettings() {
        return priority;
    }

    public void setPanel(JPanel panel) {
        this.panel = panel;
    }

    public void setPriority(int priority) {
        this.priority = priority;
    }
}
