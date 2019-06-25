package de.uka.ilkd.key.gui.extension.api;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.intern.DefaultCDockable;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import javax.swing.*;
import java.util.Collection;
import java.util.Collections;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.19)
 */
public interface TabPanel {
    @NotNull
    String getTitle();

    default @Nullable
    Icon getIcon() {
        return null;
    }

    @NotNull
    JComponent getComponent();

    /**
     * @return non-null
     */
    default @NotNull
    Collection<Action> getTitleActions() {
        return Collections.emptyList();
    }

    /**
     * @return
     */
    default @NotNull
    Collection<CAction> getTitleCActions() {
        return Collections.emptyList();
    }

    default @Nullable
    DefaultCDockable.Permissions getPermissions() {
        return null;
    }
}
