/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.match.vm.JavaMatchPlanBuilder;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.compiler.PatternKeySource;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks that the park keys of {@link ParkedBases#parkKeys} are built from operator families
 * for every taclet that ships with KeY. The families come from the taclet's own matcher
 * ({@code VMTacletMatcher#assumesKeySource}, fed by the match heads'
 * {@code topOperatorDescriptor()}) on the pattern side and from
 * {@code JavaMatchPlanBuilder#matchFamilyOf} on the concrete side; a park key and a wake key
 * only meet when the two sides agree, which is what these tests pin. A key that contains a raw
 * operator the matcher treats more liberally than operator equality can never equal a key
 * produced for a concrete sequent formula, so a base stored under it would never be woken. The
 * rule {@code referencedObjectIsCreatedRight} had this defect: its {@code \assumes} waits for a
 * {@code select} instance with a generic sort argument, which is a different operator than every
 * concrete {@code select} instance a sequent can contain.
 */
public class QueueRuleApplicationManagerWakeKeyTest {

    private static KeYEnvironment<DefaultUserInterfaceControl> env;

    @BeforeAll
    static void setUp() throws Exception {
        env = HelperClassForTests.createKeYEnvironment();
    }

    @AfterAll
    static void tearDown() {
        if (env != null) {
            env.dispose();
        }
    }

    /**
     * For every shipped taclet with an {@code \assumes} part: all park keys must be stated in
     * descriptor space. In particular no key component may be a parametric function instance
     * (the descriptor is its base), a modality (the descriptor is its kind), a schema variable,
     * or a schematic modality kind. An update application may appear as the datum of an
     * {@code ARG_OP} key (argument positions are matched as written), but never as a key's
     * head: the top of a candidate is observed with its leading updates stripped, so a head
     * naming an update application could never be met.
     */
    @Test
    void parkKeysOfAllShippedTacletsAreInDescriptorSpace() throws Exception {
        int withAssumes = 0;
        int parkable = 0;
        for (Taclet taclet : env.getInitConfig().getTaclets()) {
            if (taclet.assumesSequent().isEmpty()) {
                continue;
            }
            withAssumes++;
            final List<?> keys =
                ParkedBases.parkKeys(NoPosTacletApp.createNoPosTacletApp(taclet));
            if (keys == null) {
                continue;
            }
            parkable++;
            for (Object key : keys) {
                assertKeyInDescriptorSpace(taclet, key);
            }
        }
        // guard against silently testing nothing, for example after a rule-base loading change
        assertTrue(withAssumes > 100,
            "expected the shipped rule base to contain many assumes-taclets, got " + withAssumes);
        assertTrue(parkable > 0, "expected at least some parkable assumes-taclets");
    }

    /**
     * The defect that motivated descriptors, pinned directly: the park key of
     * {@code referencedObjectIsCreatedRight} must use the base function of the
     * {@code select<[deltaObject]>} instance, not the instance itself.
     */
    @Test
    void parametricAssumesFirstArgumentIsKeyedByItsBase() throws Exception {
        final Taclet taclet = env.getInitConfig().lookupActiveTaclet(
            new org.key_project.logic.Name("referencedObjectIsCreatedRight"));
        assertNotNull(taclet, "shipped taclet referencedObjectIsCreatedRight not found");
        final List<?> keys =
            ParkedBases.parkKeys(NoPosTacletApp.createNoPosTacletApp(taclet));
        assertNotNull(keys, "expected the taclet to be parkable");
        assertEquals(1, keys.size(), "expected one precise park key");
        final ParkedBases.WakeKey key = (ParkedBases.WakeKey) keys.get(0);
        assertEquals("ARG_OP", key.kind().toString());
        final Object datum = key.datum();
        assertTrue(datum instanceof ParametricFunctionDecl,
            "the key must hold the base function, but holds " + datum.getClass().getName());
    }

    /**
     * The pattern side and the concrete side of the key derivation must agree, or a parked base
     * could never be woken: for every shipped {@code \assumes} pattern with a concrete top, the
     * family in the matcher's key source ({@code assumesKeySource}) must equal the family
     * {@code matchFamilyOf} assigns to the pattern's own operator, and a pattern summarized as
     * unkeyable must be exactly one whose operator has no family. (For a pattern operator that
     * only stands for itself the two trivially agree; the interesting cases are the family
     * operators: parametric functions and modalities.)
     */
    @Test
    void assumesKeySourcesAgreeWithConcreteFamilies() {
        for (Taclet taclet : env.getInitConfig().getTaclets()) {
            if (!(taclet.getMatcher() instanceof VMTacletMatcher matcher)) {
                continue;
            }
            for (var sf : taclet.assumesSequent()) {
                final org.key_project.logic.Term pattern = sf.formula();
                if (pattern.op() instanceof SchemaVariable) {
                    continue;
                }
                final PatternKeySource source = matcher.assumesKeySource(pattern);
                final Object family = JavaMatchPlanBuilder.matchFamilyOf(pattern.op());
                final String where = "assumes pattern of " + taclet.name() + ": " + pattern;
                if (source instanceof PatternKeySource.ByHead byHead) {
                    assertEquals(family, byHead.headDescriptor(),
                        "pattern-side and concrete-side family differ for " + where);
                } else {
                    // An update-application pattern top is deliberately unkeyable although the
                    // operator has a family: the top position is observed stripped, so a top
                    // key naming it could never be met (VMTacletMatcher.keySourceFor).
                    assertTrue(family == null || pattern.op() instanceof UpdateApplication,
                        "pattern summarized as unkeyable although its operator has the family "
                            + family + " for " + where);
                }
            }
        }
    }

    private static void assertKeyInDescriptorSpace(Taclet taclet, Object rawKey) {
        final ParkedBases.WakeKey key = (ParkedBases.WakeKey) rawKey;
        assertComponentIsDescriptor(taclet, key.head(), "head");
        // A head naming an update application could never be met: the top of a candidate is
        // observed with its leading updates stripped. As an ARG_OP datum it is legitimate,
        // because argument positions are matched as written.
        assertFalse(key.head() instanceof UpdateApplication,
            "update application as head of a park key of " + taclet.name());
        if (key.datum() instanceof Operator datum) {
            assertComponentIsDescriptor(taclet, datum, "datum");
        }
    }

    private static void assertComponentIsDescriptor(Taclet taclet, Object value, String name) {
        assertNotNull(value, name + " of a park key of " + taclet.name());
        final String where = name + " of a park key of " + taclet.name() + ": " + value;
        assertFalse(value instanceof ParametricFunctionInstance,
            "parametric instance instead of its base as " + where);
        assertFalse(value instanceof JModality, "modality instead of its kind as " + where);
        assertFalse(value instanceof ModalOperatorSV, "schematic modality kind as " + where);
        assertFalse(value instanceof SchemaVariable, "schema variable as " + where);
    }
}
