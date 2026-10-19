/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension;

import java.util.Collection;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * The persisted enable/disable state of the FX extensions, FX counterpart of Swing
 * {@code de.uka.ilkd.key.gui.extension.impl.ExtensionSettings} (ExtensionSettings.java:13-36).
 * The same {@code "Extensions"} category and {@code "disabled"} entry key are used, so the Swing
 * app and the FX app read and write the same section of the persisted
 * {@code proofIndependentSettings.json}. Written by the checkbox panel of the settings dialog
 * ({@link ExtensionManagerF}, "applied on next restart") and honored by the extension discovery
 * of {@link KeYGuiExtensionFacadeF}: a disabled extension contributes nothing until re-enabled.
 */
public class ExtensionSettingsF extends AbstractPropertiesSettings {

    /** the category of Swing {@code ExtensionSettings} (ExtensionSettings.java:14) */
    private static final String NAME = "Extensions";

    /** the entry key of Swing {@code ExtensionSettings} (ExtensionSettings.java:15) */
    public static final String KEY_DISABLED = "disabled";

    /**
     * Class names of disabled extensions (Swing {@code forbiddenClasses}).
     */
    private final AbstractPropertiesSettings.PropertyEntry<Set<String>> forbiddenClasses =
        createStringSetProperty(KEY_DISABLED, "");

    public ExtensionSettingsF() {
        super(NAME);
    }

    public Collection<String> getForbiddenClasses() {
        return forbiddenClasses.get();
    }

    public void setForbiddenClasses(Collection<String> seq) {
        forbiddenClasses.set(new TreeSet<>(seq));
    }
}
