package de.uka.ilkd.key.gui.extension.api;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.intern.DefaultCDockable;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import javax.swing.*;
import java.util.Collection;
import java.util.Collections;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.19)
 */
public interface TabPanel {
    @Nonnull
    String getTitle();

    default @Nullable
    Icon getIcon() {
        return null;
    }

    @Nonnull
    JComponent getComponent();

    /**
     * @return non-null
     */
    default @Nonnull
    Collection<Action> getTitleActions() {
        return Collections.emptyList();
    }

    /**
     * @return
     */
    default @Nonnull
    Collection<CAction> getTitleCActions() {
        return Collections.emptyList();
    }

    default @Nullable
    DefaultCDockable.Permissions getPermissions() {
        return null;
    }
}
