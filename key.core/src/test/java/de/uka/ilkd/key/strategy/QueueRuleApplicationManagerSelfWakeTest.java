/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks, for the two hash-based {@code WakeKind}s, that parking and waking agree on concrete
 * instances: a base parked under a hash key must be found by the wake keys of every formula the
 * matcher would accept for it. The descriptor-space test
 * ({@link QueueRuleApplicationManagerWakeKeyTest}) checks the shape of park keys for all shipped
 * taclets, but it cannot check this agreement, because the hash keys only exist once the main
 * match has fixed a schema variable to a concrete term. Here real taclets are instantiated by
 * hand and the two sides are compared directly.
 */
public class QueueRuleApplicationManagerSelfWakeTest {

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

    /**
     * {@code applyEq} waits for an equality whose first argument is the term the main match
     * bound to {@code s}. Its {@link WakeKind#ARG_HASH} park key must be produced as a wake key
     * by exactly the equalities with that first argument, and not by others.
     */
    @Test
    void argHashParkKeyIsWokenByMatchingEquality() throws Exception {
        final NoPosTacletApp app =
            instantiated("applyEq", "s", tb.zTerm("42"));
        final ParkedBases.WakeKey parkKey = singleParkKey(app, "ARG_HASH");

        assertTrue(
            wakeKeysOf(tb.equals(tb.zTerm("42"), tb.zTerm("7")), parkKey).contains(parkKey),
            "an equality with the bound first argument must wake the base");
        // The negative control must differ from 42 in structure, not only in the digits:
        // hashCodeModRenaming folds the structure and sorts of a term but not function names
        // (it may only reject what matching modulo renaming would reject), so the literals 42
        // and 43 share a hash and waking on 43 = 7 would be a designed, harmless over-wake.
        assertFalse(
            wakeKeysOf(tb.equals(tb.add(tb.zTerm("4"), tb.zTerm("2")), tb.zTerm("7")), parkKey)
                    .contains(parkKey),
            "an equality with a structurally different first argument must not wake the base");
    }

    /**
     * {@code replace_known_left} waits for a formula equal to the one the main match bound to
     * {@code b}, up to renaming of bound variables. Its {@link WakeKind#WHOLE_HASH} park key
     * must be produced as a wake key by that formula, by a renamed variant of it, and by the
     * formula wrapped in an update (the matcher removes leading updates before it matches, so
     * parking and waking must compare the formula without them).
     */
    @Test
    void wholeHashParkKeyIsWokenByEqualModRenamingFormula() throws Exception {
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final LogicVariable x = new LogicVariable(new Name("selfWakeX"), intSort);
        final LogicVariable y = new LogicVariable(new Name("selfWakeY"), intSort);
        final JTerm phi = tb.all(x, tb.equals(tb.var(x), tb.var(x)));
        final JTerm phiRenamed = tb.all(y, tb.equals(tb.var(y), tb.var(y)));

        final NoPosTacletApp app = instantiated("replace_known_left", "b", phi);
        final ParkedBases.WakeKey parkKey = singleParkKey(app, "WHOLE_HASH");

        assertTrue(wakeKeysOf(phi, parkKey).contains(parkKey),
            "the bound formula itself must wake the base");
        assertTrue(wakeKeysOf(phiRenamed, parkKey).contains(parkKey),
            "a variant of the formula with renamed bound variables must wake the base");

        final LocationVariable pv =
            new LocationVariable(new ProgramElementName("selfWakeVar"), intSort);
        final JTerm wrapped = tb.apply(tb.elementary(pv, tb.zTerm("1")), phi);
        assertTrue(wakeKeysOf(wrapped, parkKey).contains(parkKey),
            "the formula wrapped in an update must wake the base");

        assertFalse(
            wakeKeysOf(phi, parkKey, !parkKey.inAntecedent()).contains(parkKey),
            "a formula on the other side of the sequent must not wake the base: assumes"
                + " formulas only match formulas of their own side");

        final JTerm other = tb.all(x, tb.equals(tb.var(x), tb.zTerm("0")));
        assertFalse(wakeKeysOf(other, parkKey).contains(parkKey),
            "a different formula must not wake the base");
    }

    /**
     * Wake keys are only computed for kinds under which some base is parked. With nothing
     * parked, a changed formula must record no keys at all, and with only an
     * {@link WakeKind#ARG_HASH} base parked it must record only keys of that kind. This is
     * what keeps proofs that park nothing free of the hash computations, which walk the whole
     * changed formula.
     */
    @Test
    void wakeKeysAreOnlyRecordedForKindsWithParkedBases() throws Exception {
        final ParkedBases empty = new ParkedBases();
        empty.recordWakeKeysOf(tb.equals(tb.zTerm("1"), tb.zTerm("2")), true);
        assertTrue(empty.pendingWakeKeys == null || empty.pendingWakeKeys.isEmpty(),
            "with nothing parked, no wake keys may be recorded");

        final NoPosTacletApp app = instantiated("applyEq", "s", tb.zTerm("42"));
        final ParkedBases.WakeKey parkKey = singleParkKey(app, "ARG_HASH");
        for (Object key : wakeKeysOf(tb.equals(tb.zTerm("42"), tb.zTerm("7")), parkKey)) {
            assertEquals("ARG_HASH", ((ParkedBases.WakeKey) key).kind().toString(),
                "only keys of kinds with parked bases may be recorded");
        }
    }

    /**
     * A base whose {@code \assumes} first argument is an update application, as in
     * {@code \assumes(p({u}x) ==>)}, is parked under an {@link WakeKind#ARG_OP} key whose datum
     * is the update application operator, and a formula whose first argument is a concrete
     * update application produces exactly that wake key. Argument positions are matched as
     * written, so the update is part of what both sides observe; only leading updates of the
     * formula itself are stripped. No shipped taclet has this shape, so the taclet is built
     * here the way a user-loaded rule would introduce it.
     */
    @Test
    void updateApplicationArgumentParkKeyIsWokenByUpdateArgumentFormula() {
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final Function p =
            new JFunction(new Name("selfWakeUpdArgP"), JavaDLTheory.FORMULA, intSort);
        final UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("selfWakeU"));
        final TermSV x = SchemaVariableFactory.createTermSV(new Name("selfWakeXsv"), intSort);
        final JTerm pattern = tb.func(p, tb.apply(tb.var(u), tb.var(x)));

        final FormulaSV find = SchemaVariableFactory.createFormulaSV(new Name("selfWakeFind"));
        final RewriteTacletBuilder<RewriteTaclet> builder = new RewriteTacletBuilder<>();
        builder.setName(new Name("selfWakeUpdArgTaclet"));
        builder.setFind(tb.var(find));
        builder.setAssumesSequent(JavaDLSequentKit.createAnteSequent(
            ImmutableList.singleton(new SequentFormula(pattern))));
        builder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), tb.var(find)));

        final NoPosTacletApp app =
            NoPosTacletApp.createNoPosTacletApp(builder.getRewriteTaclet());
        final ParkedBases.WakeKey parkKey = singleParkKey(app, "ARG_OP");
        assertEquals(p, parkKey.head(), "the key's head must be the pattern's concrete top");
        assertTrue(parkKey.datum() instanceof UpdateApplication,
            "the key's datum must be the update application family, but is " + parkKey.datum());
        assertTrue(parkKey.inAntecedent(), "the assumes formula sits in the antecedent");

        final LocationVariable pv =
            new LocationVariable(new ProgramElementName("selfWakeUpdVar"), intSort);
        final JTerm candidate =
            tb.func(p, tb.apply(tb.elementary(pv, tb.zTerm("1")), tb.zTerm("3")));
        assertTrue(wakeKeysOf(candidate, parkKey).contains(parkKey),
            "a formula with an update application as first argument must wake the base");
        assertFalse(wakeKeysOf(tb.func(p, tb.zTerm("5")), parkKey).contains(parkKey),
            "a formula whose first argument carries no update must not wake the base");
        assertFalse(wakeKeysOf(candidate, parkKey, false).contains(parkKey),
            "a formula on the other side of the sequent must not wake the base");
    }

    /** The shipped taclet of the given name with one schema variable bound to the given term. */
    private static NoPosTacletApp instantiated(String tacletName, String svName, JTerm term)
            throws Exception {
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
        return (NoPosTacletApp) app.addCheckedInstantiation(sv, term, services, true);
    }

    /** The single park key of the given application, asserting its {@code WakeKind}. */
    private static ParkedBases.WakeKey singleParkKey(NoPosTacletApp app, String expectedKind) {
        final List<ParkedBases.WakeKey> keys = ParkedBases.parkKeys(app);
        assertNotNull(keys, "expected the application to be parkable");
        assertEquals(1, keys.size(), "expected one precise park key");
        final ParkedBases.WakeKey key = keys.get(0);
        assertEquals(expectedKind, key.kind().toString());
        return key;
    }

    /**
     * The wake keys recorded for the given changed formula while one base is parked under the
     * given key. The park is needed because keys of a kind without parked bases are not
     * computed at all (see {@link ParkedBases#recordWakeKeysOf}).
     */
    private static Set<?> wakeKeysOf(JTerm formula, ParkedBases.WakeKey parkedUnder) {
        return wakeKeysOf(formula, parkedUnder, parkedUnder.inAntecedent());
    }

    /** As above, with the changed formula on the given side of the sequent. */
    private static Set<?> wakeKeysOf(JTerm formula, ParkedBases.WakeKey parkedUnder,
            boolean inAntecedent) {
        final ParkedBases parking = new ParkedBases();
        parking.parkForTests(parkedUnder, new StubRuleAppContainer());
        parking.recordWakeKeysOf(formula, inAntecedent);
        final Set<?> keys = parking.pendingWakeKeys;
        assertNotNull(keys, "recording a formula must create wake keys");
        return keys;
    }
}
