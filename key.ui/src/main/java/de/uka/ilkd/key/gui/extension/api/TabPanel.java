/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import java.util.Collection;
import java.util.Collections;
import javax.swing.*;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.intern.DefaultCDockable;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.19)
 */
public interface TabPanel {
    @NonNull
    String getTitle();

    default @Nullable Icon getIcon() {
        return null;
    }

    @NonNull
    JComponent getComponent();

    /**
     * @return non-null
     */
    default @NonNull Collection<Action> getTitleActions() {
        return Collections.emptyList();
    }

    /**
     * @return
     */
    default @NonNull Collection<CAction> getTitleCActions() {
        return Collections.emptyList();
    }

    default DefaultCDockable.@Nullable Permissions getPermissions() {
        return null;
    }
}
