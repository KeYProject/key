/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.lang.reflect.InvocationTargetException;
import java.util.Objects;

import de.uka.ilkd.key.gui.extension.ExtensionManager;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.settings.FeatureSettings;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (07.04.19)
 */
public class Extension<T> implements Comparable<Extension<T>> {
    private static final Logger LOGGER = LoggerFactory.getLogger(Extension.class);
    private final @NonNull Class<T> clazz;
    private final KeYGuiExtension.@Nullable Info info;
    private @Nullable T instance = null;

    public Extension(@NonNull Class<T> clazz) {
        this.clazz = clazz;
        this.info = clazz.getAnnotation(KeYGuiExtension.Info.class);
    }

    public T getInstance() {
        if (instance == null) {
            try {
                instance = clazz.getDeclaredConstructor().newInstance();
            } catch (InstantiationException | IllegalAccessException | NoSuchMethodException
                    | InvocationTargetException e) {
                LOGGER.warn("Failed initialize instance", e);
            }
        }
        return instance;
    }

    public String getName() {
        return info == null ? getType().getName() : info.name();
    }

    public boolean isOptional() {
        return info != null && info.optional()
                && (!isExperimental() || FeatureSettings.isFeatureActivated(getName()));
    }

    public int getPriority() {
        return info == null ? 0 : info.priority();
    }

    public boolean isDisabled() {
        return isDisabledByMaintainer() // disabled by options
                // disabled because of wrong // mode
                || (!FeatureSettings.isFeatureActivated(getName()) && isExperimental())
                // disabled by command line
                || ExtensionManager.getExtensionSettings()
                        .getForbiddenClasses().contains(getType().getName());
    }

    /**
     * @return true iff this extension was disabled by the annotation
     *         {@link de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.Info}.
     */
    public boolean isDisabledByMaintainer() {
        return info != null && info.disabled();
    }

    public boolean isExperimental() {
        return info == null || info.experimental();
    }

    public @NonNull Class<T> getType() {
        return clazz;
    }

    @Override
    public int compareTo(@NonNull Extension o) {
        return Integer.compare(getPriority(), o.getPriority());
    }


    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Extension<?> extension)) {
            return false;
        }
        return clazz.equals(extension.clazz);
    }

    @Override
    public int hashCode() {
        return Objects.hash(clazz);
    }

    public String getDescription() {
        return info == null ? "" : info.description();
    }

    public boolean supports(@NonNull Class<?> c) {
        return c.isAssignableFrom(getType());
    }

    public boolean supportsSettings() {
        return supports(KeYGuiExtension.Settings.class);
    }

    public boolean supportsLeftPanel() {
        return supports(KeYGuiExtension.LeftPanel.class);
    }

    public boolean supportsContextMenu() {
        return supports(KeYGuiExtension.ContextMenu.class);
    }

    public boolean supportsMainMenu() {
        return supports(KeYGuiExtension.MainMenu.class);
    }

    public boolean supportsStatusLine() {
        return supports(KeYGuiExtension.StatusLine.class);
    }

    public boolean supportsToolbar() {
        return supports(KeYGuiExtension.Toolbar.class);
    }

    public boolean supportsKeyboardShortcuts() {
        return supports(KeYGuiExtension.KeyboardShortcuts.class);
    }
}
