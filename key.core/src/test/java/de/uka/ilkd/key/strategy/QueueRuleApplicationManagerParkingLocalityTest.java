/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.op.Junctor;

import org.key_project.logic.op.Operator;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Pins the goal-local determinism invariant of {@link QueueRuleApplicationManager} (see its class
 * Javadoc): cloning a manager for a split goal must <em>deep</em>-copy the assumes-base
 * parking/wake
 * structures ({@code parkedByOp} / {@code pendingWakeOps}), so split siblings park and wake
 * independently. Sharing them would let one sibling's wake shift another sibling's candidate
 * birth-ages and silently change that branch's proof (a divergence no closure-only test would
 * catch). This test guards against a future "shared wake cache" / cross-goal-reuse regression.
 */
public class QueueRuleApplicationManagerParkingLocalityTest {

    @Test
    void cloneDeepCopiesParkingStructuresSoSiblingsAreIndependent() throws Exception {
        final QueueRuleApplicationManager orig = new QueueRuleApplicationManager();

        // Populate the (private) goal-local parking structures with sample state. Junctor constants
        // are convenient interned Operators; the bucket contents are irrelevant to the deep-copy.
        final LinkedHashMap<Operator, Collection<RuleAppContainer>> parked = new LinkedHashMap<>();
        final Collection<RuleAppContainer> bucket = new ArrayList<>();
        parked.put(Junctor.AND, bucket);
        final LinkedHashSet<Operator> wake = new LinkedHashSet<>();
        wake.add(Junctor.OR);
        set(orig, "parkedByOp", parked);
        set(orig, "pendingWakeOps", wake);

        final QueueRuleApplicationManager copy = (QueueRuleApplicationManager) orig.clone();

        final Object copyParked = get(copy, "parkedByOp");
        final Object copyWake = get(copy, "pendingWakeOps");
        assertNotNull(copyParked, "clone must copy parkedByOp");
        assertNotNull(copyWake, "clone must copy pendingWakeOps");
        // Deep copy: the split sibling must not share the outer structures.
        assertNotSame(parked, copyParked, "parkedByOp must be deep-copied, not shared");
        assertNotSame(wake, copyWake, "pendingWakeOps must be deep-copied, not shared");
        @SuppressWarnings("unchecked")
        final Collection<RuleAppContainer> copyBucket =
            ((LinkedHashMap<Operator, Collection<RuleAppContainer>>) copyParked).get(Junctor.AND);
        assertNotSame(bucket, copyBucket, "the per-operator parking bucket must be deep-copied");

        // Independence: a park/wake recorded on one sibling after the split must not appear on the
        // other -- this is what keeps each branch's candidate birth-ages (and thus its proof)
        // its own.
        rawAdd(bucket, new Object());
        wake.add(Junctor.IMP);
        assertTrue(copyBucket.isEmpty(),
            "a sibling's parked bucket must not see a park added to the other sibling");
        assertEquals(1, ((LinkedHashSet<?>) copyWake).size(),
            "a sibling's wake set must not see an op recorded on the other sibling");
    }

    private static void set(Object target, String field, Object value) throws Exception {
        final Field f = QueueRuleApplicationManager.class.getDeclaredField(field);
        f.setAccessible(true);
        f.set(target, value);
    }

    private static Object get(Object target, String field) throws Exception {
        final Field f = QueueRuleApplicationManager.class.getDeclaredField(field);
        f.setAccessible(true);
        return f.get(target);
    }

    @SuppressWarnings({ "unchecked", "rawtypes" })
    private static void rawAdd(Collection c, Object o) {
        c.add(o);
    }
}
