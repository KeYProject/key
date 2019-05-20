package de.uka.ilkd.key.gui.extension.api;

import bibliothek.gui.dock.common.intern.DefaultCDockable;

import javax.swing.*;
import java.util.Collection;
import java.util.Collections;

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

    default Collection<Action> getTitleActions() {
        return Collections.emptyList();
    }

    default DefaultCDockable.Permissions getPermissions() {
        return null;
    }
}
