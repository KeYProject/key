package de.uka.ilkd.key.gui.extension.api;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.19)
 */
public interface TabPanel {
    String getTitle();

    default Icon getIcon() {
        return null;
    }

    JComponent getComponent();
}
