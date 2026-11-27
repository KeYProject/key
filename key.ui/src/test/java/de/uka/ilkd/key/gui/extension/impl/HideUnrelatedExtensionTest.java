/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.pp.PosInSequent;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Contract tests for {@link HideUnrelatedExtension}: it must never contribute a context-menu item
 * (and never throw) for positions it cannot act on.
 */
class HideUnrelatedExtensionTest {

    private final HideUnrelatedExtension extension = new HideUnrelatedExtension();

    @Test
    void noItemsForNonSequentKinds() {
        assertThat(extension.getContextActions(null, ContextMenuKind.PROOF_TREE, null)).isEmpty();
        assertThat(extension.getContextActions(null, ContextMenuKind.INFO_TREE, null)).isEmpty();
    }

    @Test
    void noItemsForFullSequentPosition() {
        // A click on the sequent itself has no PosInOccurrence.
        assertThat(extension.getContextActions(null, ContextMenuKind.SEQUENT_VIEW,
            PosInSequent.createSequentPos())).isEmpty();
    }

    @Test
    void neverThrowsOnUnusableInputs() {
        // These calls must be no-ops, never NPEs.
        extension.getContextActions(null, ContextMenuKind.SEQUENT_VIEW, null);
        extension.getContextActions(null, ContextMenuKind.SEQUENT_VIEW,
            PosInSequent.createSequentPos());
    }
}
