/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.calculus;


import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.SemisequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class TestSemisequent {

    private SequentFormula[] con;

    @BeforeEach
    public void setUp() {
        TermBuilder TB = TacletForTests.services().getTermBuilder();
        Function p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, new Sort[] {});
        Function q = new JFunction(new Name("q"), JavaDLTheory.FORMULA, new Sort[] {});
        Function r = new JFunction(new Name("r"), JavaDLTheory.FORMULA, new Sort[] {});

        Function a = new JFunction(new Name("a"), JavaDLTheory.FORMULA, new Sort[] {});
        Function b = new JFunction(new Name("b"), JavaDLTheory.FORMULA, new Sort[] {});
        Function c = new JFunction(new Name("c"), JavaDLTheory.FORMULA, new Sort[] {});


        JTerm t_p = TB.func(p, new JTerm[] {});
        JTerm t_q = TB.func(q, new JTerm[] {});
        JTerm t_r = TB.func(r, new JTerm[] {});

        JTerm t_a = TB.func(a, new JTerm[] {});
        JTerm t_b = TB.func(b, new JTerm[] {});
        JTerm t_c = TB.func(c, new JTerm[] {});


        con = new SequentFormula[7];
        con[0] = new SequentFormula(t_p);
        con[1] = new SequentFormula(t_q);
        con[2] = new SequentFormula(t_r);
        con[3] = new SequentFormula(t_r);
        con[4] = new SequentFormula(t_a);
        con[5] = new SequentFormula(t_b);
        con[6] = new SequentFormula(t_c);

        Sort s = new SortImpl(new Name("test"));
        Function f = new JFunction(new Name("f"), s, new Sort[] {});
    }

    @AfterEach
    public void tearDown() {
        con = null;
    }

    private Semisequent extract(SemisequentChangeInfo semiCI) {
        return JavaDLSequentKit.createAnteSequent(semiCI.getFormulaList()).antecedent();
    }

    @Test
    public void testContains() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        SequentFormula eq2con0 =
            new SequentFormula(con[0].formula());
        assertFalse(seq.contains(eq2con0), "Contains should test of identity and not equality.");
    }

    @Test
    public void testContainsEquals() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        SequentFormula eq2con0 =
            new SequentFormula(con[0].formula());
        assertTrue(seq.containsEqual(eq2con0),
            "Contains tests of equality and should find the formula.");
    }

    @Test
    public void testGet() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        assertSame(seq.get(0), con[0]);
        assertSame(seq.get(1), con[1]);

        try {
            seq.get(2);
        } catch (IndexOutOfBoundsException iob) {
            return;
        }
        fail();
    }


    @Test
    public void testindexOf() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        seq = extract(seq.insert(2, con[2]));
        assertEquals(3, seq.size(), "Semisequent has wrong size.");
        assertEquals(0, seq.indexOf(con[0]),
            "con[0] has wrong index in semisequent. Expected 0" + " has " + seq.indexOf(con[0]));
        assertEquals(1, seq.indexOf(con[1]),
            "con[1] has wrong index in semisequent. Expected 1" + " has " + seq.indexOf(con[1]));
        assertEquals(2, seq.indexOf(con[2]),
            "con[2] has wrong index in semisequent. Expected 2" + " has " + seq.indexOf(con[2]));
    }

    @Test
    public void testRemove() {

        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        seq = extract(seq.insert(2, con[2]));
        seq = extract(seq.remove(1));

        assertEquals(2, seq.size(), "Semisequent has wrong size.");
        assertFalse(seq.contains(con[1]), "Semisequent contains deleted element.");
        assertEquals(-1, seq.indexOf(con[1]), "con[1] has wrong index in semisequent");
        assertEquals(0, seq.indexOf(con[0]), "con[0] has wrong index in semisequent");
        assertEquals(1, seq.indexOf(con[2]), "con[2] has wrong index in semisequent");
    }

    @Test
    public void testRemoveOrder() {

        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        seq = extract(seq.insert(2, con[2]));
        seq = extract(seq.insert(3, con[4]));
        seq = extract(seq.insert(4, con[5]));
        seq = extract(seq.remove(2));

        assertEquals(4, seq.size(), "Semisequent has wrong size.");
        assertFalse(seq.contains(con[2]), "Semisequent contains deleted element.");
        assertEquals(-1, seq.indexOf(con[2]), "con[1] has wrong index in semisequent");
        assertEquals(0, seq.indexOf(con[0]), "con[0] has wrong index in semisequent");
        assertEquals(1, seq.indexOf(con[1]), "con[2] has wrong index in semisequent");
        assertEquals(2, seq.indexOf(con[4]), "con[4] has wrong index in semisequent");
        assertEquals(3, seq.indexOf(con[5]), "con[4] has wrong index in semisequent");
    }

    @Test
    public void testReplace() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        seq = extract(seq.replace(1, con[2]));


        assertEquals(2, seq.size(), "Semisequent has wrong size.");
        assertFalse(seq.contains(con[1]), "Semisequent contains deleted element.");
        assertEquals(-1, seq.indexOf(con[1]), "con[1] has wrong index in semisequent");
        assertEquals(0, seq.indexOf(con[0]), "con[0] has wrong index in semisequent");
        assertEquals(1, seq.indexOf(con[2]), "con[2] has wrong index in semisequent");
    }

    @Test
    public void testNoDuplicates() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        seq = extract(seq.insert(2, con[1]));

        assertEquals(2, seq.size(), "Semisequent has duplicate");
    }


    @Test
    public void testImmutable() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        Semisequent old;
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.insert(1, con[1]));
        old = seq;
        seq = extract(seq.insert(2, con[2]));

        assertEquals(2, old.size(), "Semisequent seems not to be immutable.");
    }

    @Test
    public void testUniqueEmpty() {
        Semisequent seq = JavaDLSequentKit.emptySemisequent();
        seq = extract(seq.insert(0, con[0]));
        seq = extract(seq.remove(0));
        assertSame(JavaDLSequentKit.emptySemisequent(), seq,
            "Semisequent is empty but not the EMPTY_SEMISEQUENT.");

    }

    @Test
    public void testEquals() {
        Semisequent seq1 = JavaDLSequentKit.emptySemisequent();
        seq1 = extract(seq1.insert(0, con[0]));
        seq1 = extract(seq1.insert(0, con[1]));
        seq1 = extract(seq1.insert(0, con[2]));
        Semisequent seq2 = JavaDLSequentKit.emptySemisequent();
        seq2 = extract(seq2.insert(0, con[0]));
        seq2 = extract(seq2.insert(0, con[1]));
        seq2 = extract(seq2.insert(0, con[2]));
        Semisequent seq3 = JavaDLSequentKit.emptySemisequent();
        seq3 = extract(seq3.insert(0, con[0]));
        seq3 = extract(seq3.insert(0, con[1]));
        seq3 = extract(seq3.insert(0, con[3]));
        Semisequent seq4 = JavaDLSequentKit.emptySemisequent();
        seq4 = extract(seq4.insert(0, con[0]));
        seq4 = extract(seq4.insert(0, con[2]));
        seq4 = extract(seq4.insert(0, con[1]));

        assertEquals(seq1, seq1, "seq1=seq1");
        assertEquals(seq1, seq2, "seq1=seq2");
        assertEquals(seq1, seq3, "seq1=seq3");
        assertNotEquals(seq1, seq4, "seq1!=seq4");
    }

    @Test
    public void testListInsert() {
        Semisequent origin = extract(
            extract(
                extract(JavaDLSequentKit.emptySemisequent().insertLast(con[0])).insertLast(con[1]))
                    .insertLast(con[2]));

        Semisequent expected = extract(
            extract(extract(origin.insertLast(con[4])).insertLast(con[5])).insertLast(con[6]));
        ImmutableList<SequentFormula> insertionList = ImmutableSLList
                .<SequentFormula>nil()
                .prepend(con[0]).prepend(con[1]).prepend(con[6]).prepend(con[5]).prepend(con[4]);
        Semisequent result = extract(origin.insert(origin.size(), insertionList));
        assertEquals(expected, result, "Both semisequents should be equal.");

    }

    @Test
    public void testListInsertInMid() {
        Semisequent origin = extract(
            extract(
                extract(JavaDLSequentKit.emptySemisequent().insertLast(con[0])).insertLast(con[1]))
                    .insertLast(con[2]));
        Semisequent expected =
            extract(extract(extract(origin.insert(2, con[4])).insert(3, con[5])).insert(4, con[6]));
        ImmutableList<SequentFormula> insertionList = ImmutableSLList
                .<SequentFormula>nil()
                .prepend(con[0]).prepend(con[1]).prepend(con[6]).prepend(con[5]).prepend(con[4]);
        Semisequent result = extract(origin.insert(origin.size() - 1, insertionList));
        assertEquals(expected, result, "Both semisequents should be equal.");

    }

    @Test
    public void testListReplace() {
        // [p,q,r]
        Semisequent origin = JavaDLSequentKit
                .createAnteSequent(
                    ImmutableSLList.<SequentFormula>nil().prepend(con[0], con[1], con[2]))
                .antecedent();
        // [p,q,a,b,c]
        Semisequent expected = JavaDLSequentKit
                .createAnteSequent(origin.remove(2).getFormulaList().append(con[4], con[5], con[6]))
                .antecedent();
        // insert: [a,b,c,q,p]
        ImmutableList<SequentFormula> insertionList =
            ImmutableSLList.<SequentFormula>nil().prepend(con[4], con[5], con[6], con[1], con[0]);

        SemisequentChangeInfo result = origin.replace(origin.size() - 1, insertionList);

        assertEquals(
            ImmutableSLList.singleton(con[4]).prepend(con[5]).prepend(con[6]),
            result.addedFormulas(),
            "SemisequentChangeInfo is corrupt due to wrong added formula list:");
        assertEquals(ImmutableSLList.singleton(con[2]),
            result.removedFormulas(),
            "SemisequentChangeInfo is corrupt due to wrong removed formula list:");
        assertEquals(expected, extract(result), "Both semisequents should be equal.");

    }

    @Test
    public void testListReplaceAddRedundantList() {
        // [p,q]
        Semisequent origin =
            extract(
                extract(JavaDLSequentKit.emptySemisequent().insertLast(con[0])).insertLast(con[1]));
        // [exp.: p,q,a,b,c,r]
        Semisequent expected = extract(extract(
            extract(extract(origin.insertLast(con[4])).insertLast(con[5])).insertLast(con[6]))
                .insertLast(con[2]));
        // insert:[a,b,c,r,r,q,p]
        ImmutableList<SequentFormula> insertionList =
            ImmutableSLList.singleton(con[0]).prepend(con[1]).prepend(con[2])
                    .prepend(con[3]).prepend(con[6]).prepend(con[5]).prepend(con[4]);

        SemisequentChangeInfo sci = origin.replace(origin.size(), insertionList);
        assertEquals(
            ImmutableSLList.singleton(con[4]).prepend(con[5]).prepend(con[6])
                    .prepend(con[3]),
            sci.addedFormulas(),
            "SemisequentChangeInfo is corrupt due to wrong added formula list:");
        assertEquals(ImmutableSLList.<SequentFormula>nil(), sci.removedFormulas(),
            "SemisequentChangeInfo is corrupt due to wrong removed formula list:");
        assertEquals(expected, extract(sci), "Both semisequents should be equal.");
    }

    @Test
    void constructorTest() {
        var a = JavaDLSequentKit.emptySemisequent();
        var b = JavaDLSequentKit.createAnteSequent(ImmutableSLList.nil()).antecedent();
        assertSame(a, b);
    }

}
