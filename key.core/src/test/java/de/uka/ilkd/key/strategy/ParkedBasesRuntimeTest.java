/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.ParkedBases.WakeKey;
import de.uka.ilkd.key.strategy.ParkedBases.WakeKind;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks the runtime cycle of {@link ParkedBases} with real taclet applications: a base parked
 * under its derived keys is returned by {@link ParkedBases#drainWoken()} exactly once when a
 * matching formula is recorded, leaves the parked map through the key recomputation of the
 * unindexing, and the woken bases of one round come out one {@link WakeKind} at a time in the
 * fixed wake order, which the queue turns into the proof-relevant insertion order. The key
 * derivation itself and the park-versus-wake agreement on formula shapes are covered by
 * {@link QueueRuleApplicationManagerWakeKeyTest} and
 * {@link QueueRuleApplicationManagerSelfWakeTest}.
 */
public class ParkedBasesRuntimeTest {

    private static KeYEnvironment<DefaultUserInterfaceControl> env;
    private static Services services;
    private static TermBuilder tb;

    @BeforeAll
    static void setUp() throws Exception {
        env = HelperClassForTests.createKeYEnvironment();
        services = env.getServices();
        tb = services.getTermBuilder();
    }

    @AfterAll
    static void tearDown() {
        if (env != null) {
            env.dispose();
        }
    }

    @Test
    void wokenBaseIsDrainedOnceAndReleased() {
        final ParkedBases parking = new ParkedBases();
        final TacletAppContainer base = container("applyEq", "s", tb.zTerm("42"));
        final WakeKey key = park(parking, base);
        assertEquals(WakeKind.ARG_HASH, key.kind());

        final JTerm completer = tb.equals(tb.zTerm("42"), tb.zTerm("7"));
        parking.recordWakeKeysOf(completer, key.inAntecedent());
        final Collection<RuleAppContainer> woken = parking.drainWoken();
        assertEquals(1, woken.size(), "the parked base must be woken");
        assertSame(base, woken.iterator().next(), "the woken base is the parked one");
        assertTrue(parking.parkedMapForTests().isEmpty(),
            "unindexing recomputes the base's keys and releases it from the map");

        parking.recordWakeKeysOf(completer, key.inAntecedent());
        assertTrue(parking.drainWoken().isEmpty(),
            "with nothing parked a second change wakes nothing");
    }

    @Test
    void unmatchedChangesWakeNothing() {
        final ParkedBases parking = new ParkedBases();
        final TacletAppContainer base = container("applyEq", "s", tb.zTerm("42"));
        final WakeKey key = park(parking, base);

        // the right formula on the wrong side, then a structurally different one on the right side
        parking.recordWakeKeysOf(tb.equals(tb.zTerm("42"), tb.zTerm("7")), !key.inAntecedent());
        parking.recordWakeKeysOf(tb.equals(tb.add(tb.zTerm("4"), tb.zTerm("2")), tb.zTerm("7")),
            key.inAntecedent());
        assertTrue(parking.drainWoken().isEmpty(), "no recorded change matches the parked key");
        assertEquals(1, parking.parkedMapForTests().size(), "the base stays parked");
    }

    @Test
    void drainCollectsOneKindAtATimeInWakeOrder() {
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final LogicVariable x = new LogicVariable(new Name("runtimeX"), intSort);
        final JTerm phi = tb.all(x, tb.equals(tb.var(x), tb.var(x)));

        final ParkedBases parking = new ParkedBases();
        final TacletAppContainer argHashBase = container("applyEq", "s", tb.zTerm("42"));
        final TacletAppContainer wholeHashBase = container("replace_known_left", "b", phi);
        // Parked in the opposite of the wake order, so a passing test cannot be an accident of
        // insertion: ARG_HASH is collected before WHOLE_HASH regardless.
        final WakeKey wholeKey = park(parking, wholeHashBase);
        final WakeKey argKey = park(parking, argHashBase);
        assertEquals(WakeKind.WHOLE_HASH, wholeKey.kind());
        assertEquals(WakeKind.ARG_HASH, argKey.kind());

        parking.recordWakeKeysOf(tb.equals(tb.zTerm("42"), tb.zTerm("7")), argKey.inAntecedent());
        parking.recordWakeKeysOf(phi, wholeKey.inAntecedent());
        final Collection<RuleAppContainer> woken = parking.drainWoken();
        assertEquals(2, woken.size(), "both bases must wake");
        final Iterator<RuleAppContainer> it = woken.iterator();
        assertSame(argHashBase, it.next(), "the ARG_HASH kind is collected first");
        assertSame(wholeHashBase, it.next(), "the WHOLE_HASH kind is collected last");
        assertNotNull(parking.parkedMapForTests());
        assertTrue(parking.parkedMapForTests().isEmpty(), "both bases left the map");
    }

    /** Parks the container under its single derived key and returns that key. */
    private static WakeKey park(ParkedBases parking, TacletAppContainer base) {
        final List<WakeKey> keys = ParkedBases.parkKeys(base.getTacletApp());
        assertNotNull(keys, "expected the application to be parkable");
        assertEquals(1, keys.size(), "expected one precise park key");
        parking.parkForTests(keys.get(0), base);
        return keys.get(0);
    }

    /** A container over the shipped taclet with one schema variable bound to the given term. */
    private static TacletAppContainer container(String tacletName, String svName, JTerm term) {
        final Taclet taclet = env.getInitConfig().lookupActiveTaclet(new Name(tacletName));
        assertNotNull(taclet, "shipped taclet " + tacletName + " not found");
        NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);
        SchemaVariable sv = null;
        for (SchemaVariable v : app.uninstantiatedVars()) {
            if (v.name().toString().equals(svName)) {
                sv = v;
            }
        }
        assertNotNull(sv, "schema variable " + svName + " not found in " + tacletName);
        final NoPosTacletApp bound =
            (NoPosTacletApp) app.addCheckedInstantiation(sv, term, services, true);
        return new NoFindTacletAppContainer(bound, NumberRuleAppCost.getZeroCost(), true,
            NumberRuleAppCost.getZeroCost(), -1);
    }
}
