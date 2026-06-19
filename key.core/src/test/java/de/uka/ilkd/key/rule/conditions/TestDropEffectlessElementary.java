/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.rule.conditions.DropEffectlessElementariesCondition.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestDropEffectlessElementary {

    @Test
    public void testSelfAssignments() {

        JTerm term = TacletForTests.parseTerm("{ i := i }(i=0)");
        JTerm result = applyDrop(term);
        assertEquals(term, result);

        term = TacletForTests.parseTerm("{ i := i || i := 0 }(i=0)");
        result = applyDrop(term);
        JTerm expected = TacletForTests.parseTerm("{i:=0}(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ i := 0 || i := i }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("{i:=i}(i=0)");
        assertEquals(expected, result);
    }

    @Test
    public void testDoubleAssignment() {

        JTerm term = TacletForTests.parseTerm("{ i := j || j := i }(i=0)");
        JTerm result = applyDrop(term);
        JTerm expected = TacletForTests.parseTerm("{i := j}(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ j := 5 || j := j }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ i:=i || j := 5 || i:=i || j := j }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("{i:=i}(i=0)");
        assertEquals(expected, result);
    }

    // this was bug #1269
    @Test
    public void testFaultyCase() {
        // The parser cannot parse this but this can appear as
        // result of the sequential to parallel of {i:=i+1}{i:=i}

        JTerm term;
        // Term term = TacletForTests.parseTerm("{ {i := i+1}i:=i }(i=0)");
        {
            JTerm t0 = TacletForTests.parseTerm("{i := i+1}0").sub(0);
            JTerm t1 = TacletForTests.parseTerm("{i := i}0").sub(0);
            JTerm t2 = TacletForTests.parseTerm("i=0");
            TermBuilder tb = TacletForTests.services().getTermBuilder();

            JTerm t3 = tb.apply(t0, t1, null);
            term = tb.apply(t3, t2, null);
        }
        assertEquals("{{i:=i + 1}i:=i}(i = 0)",
            LogicPrinter.quickPrintTerm(term, TacletForTests.services));

        JTerm result = applyDrop(term);
        assertEquals(term, result);
    }

    // the following cannot be parsed apparently.
    // public void testUpdatedUpdate() throws Exception {
    // Term term = TacletForTests.parseTerm("({i:=i}{i := i})(i=0)");
    // Term result = applyDrop(term);
    // Term expected = TacletForTests.parseTerm("i=0");
    // assertEquals(expected, result);
    //
    // term = TacletForTests.parseTerm("({i:=i}{j:=5})(i=0)");
    // result = applyDrop(term);
    // expected = TacletForTests.parseTerm("(i=0)");
    // assertEquals(expected, result);
    // }

    /**
     * Original implementation: collect <em>all</em> program variables occurring in {@code target}
     * (a full walk of the term and the Java program it contains), then let the helper test the
     * update's LHS variables against them.
     */
    static JTerm dropEffectlessElementariesFull(JTerm update, JTerm target,
            Services services) {
        TermProgramVariableCollector collector = services.getFactory().create(services);
        target.execPostOrder(collector);
        Set<LocationVariable> varsInTarget = collector.result();
        JTerm simplifiedUpdate = dropEffectlessElementariesHelper(update, varsInTarget, services);
        return simplifiedUpdate == null ? null
                : services.getTermBuilder().apply(simplifiedUpdate, target, null);
    }

    /**
     * The default (targeted occurrence search) and the reference (full collection) implementations
     * of {@code \dropEffectlessElementaries} must always produce the same term -- including for
     * modality targets, where the relevant variables occur inside the Java program rather than in
     * the surrounding first-order formula.
     */
    @Test
    public void testFullTargetedEquivalence() {
        final String[] cases = {
            "{ i := i }(i=0)",
            "{ i := i || i := 0 }(i=0)",
            "{ i := 0 || i := i }(i=0)",
            "{ i := j || j := i }(i=0)",
            "{ j := 5 || j := j }(i=0)",
            "{ i:=i || j := 5 || i:=i || j := j }(i=0)",
            "{ i := 5 }\\<{ i = i+1; }\\>(i=6)",
            "{ j := 5 }\\<{ i = i+1; }\\>(i=1)",
            "{ i := 5 || j := 7 }\\<{ i = i+1; }\\>(i>0)",
            // heap is special (see testHeapProgramVariable): both implementations must treat it
            // the same -- kept under a non-empty modality, dropped without one if it does not
            // occur.
            "{ heap := savedHeap }\\<{ i = i+1; }\\>(i=6)",
            "{ i := 5 || heap := savedHeap }\\<{ i = i+1; }\\>(i=6)",
            "{ heap := savedHeap }(i=0)",
            "{ heap := savedHeap }(heap = heap)" };

        final Services services = TacletForTests.services();
        for (String s : cases) {
            JTerm term = TacletForTests.parseTerm(s);
            JTerm update = term.sub(0);
            JTerm target = term.sub(1);
            JTerm full = dropEffectlessElementariesFull(update, target, services);
            JTerm targeted = dropEffectlessElementariesTargeted(update, target, services);
            // Equal terms (not necessarily the same object: the reference implementation itself is
            // not identity-stable for every update, since the result is freshly built via the
            // TermBuilder -- the targeted search introduces no additional difference).
            assertEquals(full, targeted, "full and targeted disagree for: " + s);
        }
    }

    /**
     * The heap variable is a special case: {@code ProgramVariableCollector} seeds <em>all</em> heap
     * variables as soon as a non-empty modality is present, so an update of {@code heap} is never
     * effectless under a modality -- even when {@code heap} does not occur in the program. Without
     * a
     * modality, {@code heap} behaves like any other variable: relevant only if it actually occurs.
     * ({@code heap := savedHeap} is used as an arbitrary heap modification -- deliberately not a
     * self-assignment {@code heap := heap}, which an unrelated rule might drop -- since the
     * condition
     * only inspects the left-hand side.)
     */
    @Test
    public void testHeapProgramVariable() {
        // Under a non-empty modality, the heap update is kept although heap is absent from the
        // program (i is used in the program, so its update is kept too): nothing is dropped.
        JTerm term =
            TacletForTests.parseTerm("{ i := 5 || heap := savedHeap }\\<{ i = i+1; }\\>(i = 6)");
        assertEquals(term, applyDrop(term));

        // Heap also stays when it occurs in the target itself.
        term = TacletForTests.parseTerm("{ heap := savedHeap }(heap = heap)");
        assertEquals(term, applyDrop(term));

        // Without a modality and without an occurrence of heap, the heap update is dropped.
        term = TacletForTests.parseTerm("{ heap := savedHeap }(i = 0)");
        assertEquals(TacletForTests.parseTerm("(i = 0)"), applyDrop(term));
    }

    private JTerm applyDrop(JTerm term) {

        JTerm update = term.sub(0);
        JTerm arg = term.sub(1);

        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable x = SchemaVariableFactory.createFormulaSV(new Name("x"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));
        DropEffectlessElementariesCondition cond =
            new DropEffectlessElementariesCondition(u, x, result);

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(u, update, TacletForTests.services());
        svInst = svInst.add(x, arg, TacletForTests.services());

        MatchConditions mc = MatchConditions.EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        // first 2 args are not used in the following method, hence, can be null.
        mc = (MatchConditions) cond.check(null, null, mc, TacletForTests.services());

        if (mc == null) {
            return term;
        }

        return mc.getInstantiations().getTermInstantiation(result, null, TacletForTests.services());
    }

}
