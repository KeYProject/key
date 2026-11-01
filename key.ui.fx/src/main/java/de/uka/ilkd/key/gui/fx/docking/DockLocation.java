/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

/**
 * The role areas of the {@link DockWorkspace}, mirroring the {@code CGrid} roles of
 * {@code DockingHelper} in the Swing module {@code key.ui}.
 */
public enum DockLocation {
    /** The left panel (proof tree, info view, strategy selection, ...). */
    LEFT,
    /** The central panel (goal list, sequent view, ...). */
    MAIN,
    /** The right panel (source view, ...). */
    RIGHT
}
