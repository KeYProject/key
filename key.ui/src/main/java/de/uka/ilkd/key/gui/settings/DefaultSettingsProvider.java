/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class DefaultSettingsProvider implements SettingsProvider {
    private String description;
    private JComponent panel;
    private List<SettingsProvider> children;
    private final String keywords = "";
    private int priority;
    private Icon icon;

    public DefaultSettingsProvider() {
    }

    public DefaultSettingsProvider(String desc, JComponent pane) {
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
    public JComponent getPanel(MainWindow window) {
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
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
    }

    @Override
    public Icon getIcon() {
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

    public void setPanel(JComponent panel) {
        this.panel = panel;
    }

    public void setPriority(int priority) {
        this.priority = priority;
    }
}
