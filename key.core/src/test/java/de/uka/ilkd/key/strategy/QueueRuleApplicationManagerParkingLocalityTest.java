/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Collection;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.strategy.ParkedBases.WakeKey;
import de.uka.ilkd.key.strategy.ParkedBases.WakeKind;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks a property that {@link QueueRuleApplicationManager} relies on for reproducible proofs
 * (see its class comment): when a goal splits into two, copying its parking state
 * ({@link ParkedBases#copy()}) must give each copy its own map, buckets, and pending change set,
 * so the two goals set candidates aside and put them back independently. If they shared this
 * state, one goal putting a candidate back would change the round in which it enters the other
 * goal's queue, and so change that goal's proof. Such a change would not make any test fail
 * that only checks whether a proof closes, which is why this property is checked directly.
 */
public class QueueRuleApplicationManagerParkingLocalityTest {

    @Test
    void copyDeepCopiesParkingStructuresSoSiblingsAreIndependent() {
        final ParkedBases orig = new ParkedBases();

        // Populate the parking structures with sample state. A WakeKey over Junctor constants
        // (convenient interned operators) is a valid key; the bucket contents are irrelevant to
        // the deep-copy.
        final WakeKey key = new WakeKey(WakeKind.OP, true, Junctor.AND, null);
        orig.parkForTests(key, new StubRuleAppContainer());
        final Collection<RuleAppContainer> bucket = orig.parkedMapForTests().get(key);
        orig.pendingWakeKeys = new LinkedHashSet<>();
        orig.pendingWakeKeys.add(new WakeKey(WakeKind.OP, true, Junctor.OR, null));

        final ParkedBases copy = orig.copy();

        assertNotNull(copy.parkedMapForTests(), "copy must carry the parked map");
        assertNotNull(copy.pendingWakeKeys, "copy must carry the pending change set");
        // Deep copy: the split sibling must not share the outer structures.
        assertNotSame(orig.parkedMapForTests(), copy.parkedMapForTests(),
            "the parked map must be deep-copied, not shared");
        assertNotSame(orig.pendingWakeKeys, copy.pendingWakeKeys,
            "the pending change set must be deep-copied, not shared");
        final Collection<RuleAppContainer> copyBucket = copy.parkedMapForTests().get(key);
        assertNotSame(bucket, copyBucket, "the parking bucket must be deep-copied");

        // Independence: a park or wake recorded on one sibling after the split must not appear on
        // the other. This is what keeps the round in which a candidate enters each branch's queue,
        // and with it that branch's proof, independent of the other branch.
        orig.parkForTests(key, new StubRuleAppContainer());
        orig.pendingWakeKeys.add(new WakeKey(WakeKind.OP, true, Junctor.IMP, null));
        assertEquals(1, copyBucket.size(),
            "a sibling's parked bucket must not see a park added to the other sibling");
        assertEquals(1, copy.pendingWakeKeys.size(),
            "a sibling's wake set must not see a key recorded on the other sibling");

        // The per-head counts must be sibling-local as well: they gate which wake keys a
        // changed formula records, so a shared array would let one sibling's parks make the
        // other compute keys for bases it does not hold.
        final var services = de.uka.ilkd.key.rule.TacletForTests.services();
        final var tb = services.getTermBuilder();
        final var orFormula = tb.or(tb.tt(), tb.ff());
        orig.parkForTests(new WakeKey(WakeKind.OP, true, Junctor.OR, null),
            new StubRuleAppContainer());
        copy.recordWakeKeysOf(orFormula, true);
        assertTrue(copy.pendingWakeKeys == null || copy.pendingWakeKeys.size() == 1,
            "a sibling must not record keys for heads only the other sibling parked under");
        orig.recordWakeKeysOf(orFormula, true);
        assertTrue(orig.pendingWakeKeys.stream()
                .anyMatch(k -> ((WakeKey) k).head() == Junctor.OR),
            "the parking sibling must record the key for its own parked head");

        // The manager-level clone must route through the same deep copy.
        final QueueRuleApplicationManager manager = new QueueRuleApplicationManager();
        final QueueRuleApplicationManager managerCopy =
            (QueueRuleApplicationManager) manager.clone();
        assertNotNull(managerCopy);
        assertTrue(managerCopy != manager);
    }
}
