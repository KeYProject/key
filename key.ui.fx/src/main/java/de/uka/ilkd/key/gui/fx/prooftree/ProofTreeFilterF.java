/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

/**
 * One filter of the proof tree (reviewer request: the filters are factored out of the tree so
 * adding a filter consists of adding a class and one {@code addFilter(...)} registration line in
 * the {@link ProofTreeViewF} constructor).
 * <p>
 * The state of a filter lives outside the tree (usually {@code
 * ProofIndependentSettings.getViewSettings()}, like the Swing {@code ProofTreeViewFilter}), so it
 * persists and is shared with the classic UI. Different filter types are possible: the
 * collapsible search is a structural filter realized inside {@link ProofTreeViewF} itself (it
 * needs the query state), while the boolean ViewSettings-backed filters are
 * {@link ViewSettingsFilterF} instances.
 */
public interface ProofTreeFilterF {

    /**
     * @return the label of the filter toggle in the proof tree context menu (the Swing
     *         "Settings" checkbox label)
     */
    String name();

    /**
     * @return whether the filter is currently active
     */
    boolean isActive();

    /**
     * Sets the active state of the filter (written to the persistent settings).
     *
     * @param active the new state
     */
    void setActive(boolean active);

    /**
     * @param other another registered filter
     * @return whether activating {@code this} must deactivate {@code other} (Swing: activating
     *         one node filter deactivates the other, ProofTreeViewFilter)
     */
    default boolean isExclusiveWith(ProofTreeFilterF other) {
        return false;
    }
}
