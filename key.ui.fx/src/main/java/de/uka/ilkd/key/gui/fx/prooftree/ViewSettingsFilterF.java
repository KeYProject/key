/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import java.util.Objects;
import java.util.function.BiConsumer;
import java.util.function.Function;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * A boolean proof tree filter backed by a {@link ViewSettings} flag — the common case of the
 * Swing {@code ProofTreeViewFilter} checkboxes (Hide Intermediate Proofsteps, Hide Automode
 * Proofsteps, Hide Closed Subtrees, Hide Subtrees whose Goals are Interactive). The state is read
 * from and written to the settings, so it persists and is shared with the classic UI.
 * <p>
 * Two filters constructed with the same (non-null) exclusivity group deactivate each other when
 * one is activated (Swing: only one node filter is active at a time).
 *
 * @param name the label of the filter toggle
 * @param getter reads the flag from the settings
 * @param setter writes the flag to the settings
 * @param exclusiveGroup the exclusivity group, {@code null} for no exclusivity
 */
public record ViewSettingsFilterF(String name, Function<ViewSettings, Boolean> getter,
        BiConsumer<ViewSettings, Boolean> setter, String exclusiveGroup)
        implements ProofTreeFilterF {

    /** The exclusivity group of the two node filters (Swing: only one node filter at a time). */
    public static final String NODE_FILTER_GROUP = "node";

    @Override
    public String name() {
        return name;
    }

    @Override
    public boolean isActive() {
        return getter.apply(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings());
    }

    @Override
    public void setActive(boolean active) {
        setter.accept(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings(), active);
    }

    @Override
    public boolean isExclusiveWith(ProofTreeFilterF other) {
        return exclusiveGroup != null && other instanceof ViewSettingsFilterF vsf
                && Objects.equals(exclusiveGroup, vsf.exclusiveGroup);
    }
}
