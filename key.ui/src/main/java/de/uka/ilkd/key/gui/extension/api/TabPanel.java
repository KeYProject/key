/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import java.util.Collection;
import java.util.Collections;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.intern.DefaultCDockable;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.19)
 */
public interface TabPanel {
    @Nonnull
    String getTitle();

    default @Nullable Icon getIcon() {
        return null;
    }

    @Nonnull
    JComponent getComponent();

    /**
     * @return non-null
     */
    default @Nonnull Collection<Action> getTitleActions() {
        return Collections.emptyList();
    }

    /**
     * @return
     */
    default @Nonnull Collection<CAction> getTitleCActions() {
        return Collections.emptyList();
    }

    default @Nullable DefaultCDockable.Permissions getPermissions() {
        return null;
    }
}
