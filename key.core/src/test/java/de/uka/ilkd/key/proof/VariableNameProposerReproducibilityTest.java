/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.AbstractProfile;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link VariableNameProposer#getNameProposal} (used by the {@code \obtain} script command, whose
 * Skolem constant enters the proof) must derive the name from the current namespace occupancy
 * alone,
 * not from a proof-global counter -- otherwise the proposal is not reproducible across
 * prune-and-redo or reload (#3851).
 */
class VariableNameProposerReproducibilityTest {

    private static Services freshServices() {
        return new Services(AbstractProfile.getDefaultProfile());
    }

    private static void occupy(Services services, String name) {
        services.getNamespaces().sorts().add(new SortImpl(new Name(name), ImmutableSet.empty(),
            false));
    }

    /** Two calls with an unchanged namespace must yield the same name. */
    @Test
    void sameNamespaceYieldsSameProposal() {
        Services services = freshServices();
        occupy(services, "x"); // force a suffix to be appended
        String first = VariableNameProposer.DEFAULT.getNameProposal("x", services, null);
        String second = VariableNameProposer.DEFAULT.getNameProposal("x", services, null);
        assertEquals(first, second,
            "an unchanged namespace must give the same proposal (a proof-global counter would not)");
        assertEquals("x0", first);
    }

    /** The proposal is the smallest free index against the namespace. */
    @Test
    void picksSmallestFreeIndex() {
        Services services = freshServices();
        assertEquals("x", VariableNameProposer.DEFAULT.getNameProposal("x", services, null));
        occupy(services, "x");
        assertEquals("x0", VariableNameProposer.DEFAULT.getNameProposal("x", services, null));
        occupy(services, "x0");
        assertEquals("x1", VariableNameProposer.DEFAULT.getNameProposal("x", services, null));
    }
}
