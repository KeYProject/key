/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * class tests the term factory
 */
public class TestTermFactory {


    private JTerm et1;
    private final Sort sort1 = new SortImpl(new Name("S1"));
    private final Sort sort2 = new SortImpl(new Name("S2"));
    private final Sort sort3 = new SortImpl(new Name("S3"));
    private final Sort osort1 = new SortImpl(new Name("os1"));
    private final Sort osort2 = new SortImpl(new Name("os2"), osort1);
    private final Sort osort3 = new SortImpl(new Name("os3"), osort1);
    private final Sort osort4 = new SortImpl(new Name("os4"),
        DefaultImmutableSet.<Sort>nil().add(osort2).add(osort3), false);

    final Function p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, sort1);
    // p(:S1):BOOL
    final LogicVariable x = new LogicVariable(new Name("x"), sort1); // x:S1
    final Function q =
        new JFunction(new Name("q"), JavaDLTheory.FORMULA, new SortImpl(new Name("Whatever")));
    // q(:Whatever):BOOL
    final LogicVariable z = new LogicVariable(new Name("z"), sort1); // z:S1
    final Function r = new JFunction(new Name("r"), JavaDLTheory.FORMULA, sort1, sort2);
    // r(:S1, :S2):BOOL
    final LogicVariable y = new LogicVariable(new Name("y"), sort3); // y:S3
    final LogicVariable w = new LogicVariable(new Name("w"), sort2); // w:S2
    final Function f = new JFunction(new Name("f"), sort1, sort3);
    // f(:S3):S1

    final LogicVariable v1 = new LogicVariable(new Name("v1"), osort1);
    final LogicVariable v2 = new LogicVariable(new Name("v2"), osort2);
    final LogicVariable v3 = new LogicVariable(new Name("v3"), osort3);
    final LogicVariable v4 = new LogicVariable(new Name("v4"), osort4);

    final Function g = new JFunction(new Name("g"), osort3, osort2, osort1);
    private TermBuilder TB;
    private TermFactory tf;


    @BeforeEach
    public void setUp() {
        JTerm et_x = new TermImpl(x, new ImmutableArray<>(), null, null);
        JTerm et_px = new TermImpl(p, new ImmutableArray<>(et_x), null, null);
        et1 = et_px;
        TB = TacletForTests.services().getTermBuilder();
        tf = TB.tf();
    }

    private JTerm t1() {
        JTerm t_x = tf.createTerm(x);
        JTerm t_px = tf.createTerm(p, t_x);
        return t_px;
    }

    private JTerm t2() {
        JTerm t_x = tf.createTerm(x);
        JTerm t_w = tf.createTerm(w);
        return tf.createTerm(r, t_x, t_w);
    }

    private JTerm t3() {
        JTerm t_y = tf.createTerm(y);
        return tf.createTerm(f, t_y);
    }


    @Test
    public void testWrongSorts() {

        Exception exc = new Exception();
        try {
            JTerm t_z = tf.createTerm(z);
            JTerm t_pz = tf.createTerm(q, t_z);
        } catch (TermCreationException e) {
            exc = e;

        }
        assertTrue(exc instanceof TermCreationException);
    }

    @Test
    public void testSimplePredicate() {
        assertEquals(t1(), et1);
    }

    @Test
    public void testWrongArity() {

        Exception exc = null;
        try {
            JTerm t_x = tf.createTerm(x);
            tf.createTerm(r, t_x);
        } catch (TermCreationException e) {
            exc = e;
        }
        assertNotNull(exc, "expected TermCreationException but got " + exc);
    }

    /**
     * subformulae are invalid built, but the term shall be constructed anyway, as subformulae are
     * not checked
     */
    @Test
    public void testWithInvalidSubformulae() {
        JTerm invalidBuilt = new TermImpl(p,
            new ImmutableArray<>(new TermImpl(y, new ImmutableArray<>(), null, null)), null, null);
        try {
            JTerm t_px_or_py = tf.createTerm(Junctor.OR, invalidBuilt, t1());
        } catch (Exception e) {
            fail();
        }
    }

    @Test
    public void testConstantTrue() {
        JTerm t_true = tf.createTerm(Junctor.TRUE);
        assertEquals(t_true, new TermImpl(Junctor.TRUE, new ImmutableArray<>(), null, null));
    }

    @Test
    public void testQuantifierTerm() {
        JTerm t_forallx_px = TB.all(ImmutableSLList.<QuantifiableVariable>nil().append(x), t1());
        assertEquals(t_forallx_px, new TermImpl(Quantifier.ALL, new ImmutableArray<>(t1()),
            new ImmutableArray<>(x), null));
    }

    @Test
    public void testJunctorTerm() {
        JTerm t_px_imp_ryw = tf.createTerm(Junctor.IMP, t1(), t2());
        assertEquals(t_px_imp_ryw,
            new TermImpl(Junctor.IMP, new ImmutableArray<>(t1(), t2()), null, null));
    }

    @Test
    public void testNegationTerm() {
        JTerm t_not_ryw = tf.createTerm(Junctor.NOT, t2());
        assertEquals(t_not_ryw, new TermImpl(Junctor.NOT, new ImmutableArray<>(t2()), null, null));
    }

    @Test
    public void testDiamondTerm() {
        JavaBlock jb = JavaBlock.EMPTY_JAVABLOCK;
        JTerm t_dia_ryw = tf.createTerm(JModality.getModality(JModality.JavaModalityKind.DIA, jb),
            new JTerm[] { t2() }, null, null);
        assertEquals(t_dia_ryw,
            new TermImpl(JModality.getModality(JModality.JavaModalityKind.DIA, jb),
                new ImmutableArray<>(t2()), null));
    }

    @Test
    public void testBoxTerm() {
        JavaBlock jb = JavaBlock.EMPTY_JAVABLOCK;
        JTerm t_dia_ryw = tf.createTerm(JModality.getModality(JModality.JavaModalityKind.BOX, jb),
            new ImmutableArray<>(t2()), null, null);
        assertEquals(t_dia_ryw,
            new TermImpl(JModality.getModality(JModality.JavaModalityKind.BOX, jb),
                new ImmutableArray<>(t2()), null));
    }

    @Test
    public void testSubstitutionTerm() {
        JTerm t_x_subst_fy_in_px = TB.subst(WarySubstOp.SUBST, x, t3(), t1());
        assertEquals(new TermImpl(WarySubstOp.SUBST, new ImmutableArray<>(t3(), t1()),
            new ImmutableArray<>(x), null), t_x_subst_fy_in_px);
    }


    @Test
    public void testWrongSubstTermForLogicVariable() {
        Exception exc = new Exception();
        try {
            tf.createTerm(WarySubstOp.SUBST, new JTerm[] { t2(), t1() }, new ImmutableArray<>(x),
                null);
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
    }

    @Test
    public void testSubtermsForLogicVariable() {
        Exception exc = new Exception();
        try {
            tf.createTerm(x, t3());
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException,
            "Expected " + exc + " to be of type TermCreation but was: " + exc.getClass().getName());
    }


    @Test
    public void testQuantifierWithNoBoundSubTerms() {
        JTerm result = null;
        try {
            result = TB.all(ImmutableSLList.nil(), t1());
        } catch (TermCreationException e) {
        }
        assertEquals(result, t1());
    }


    @Test
    public void testJunctorTermWithWrongArity() {
        Exception exc = new Exception();
        try {
            tf.createTerm(Junctor.NOT, t1(), t2());
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
    }


    @Test
    public void testSubSorts1() {
        tf.createTerm(g, tf.createTerm(v4), tf.createTerm(v1));
        tf.createTerm(g, tf.createTerm(v4), tf.createTerm(v4));
        tf.createTerm(g, tf.createTerm(v2), tf.createTerm(v3));
        Exception exc = new Exception();
        try {
            tf.createTerm(g, tf.createTerm(v1), tf.createTerm(v1));
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
        exc = new Exception();
        try {
            tf.createTerm(g, tf.createTerm(y), tf.createTerm(y));
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
    }

    @Test
    public void testSubSortsEquals() {
        tf.createTerm(Equality.EQUALS, tf.createTerm(v4), tf.createTerm(v1));
        tf.createTerm(Equality.EQUALS, tf.createTerm(v4), tf.createTerm(v4));
        tf.createTerm(Equality.EQUALS, tf.createTerm(v2), tf.createTerm(v3));
        tf.createTerm(Equality.EQUALS, tf.createTerm(x), tf.createTerm(z));
        // Exception exc = null;
        // try { XXX
        // tf.createEqualityTerm(tf.createVariableTerm(v1),
        // TB.skip());
        // } catch (TermCreationException e) {
        // exc=e;
        // }
        // assertTrue("Expected TermCreationException. But was:" + exc,
        // exc instanceof TermCreationException);
        // exc = null;
        // try {
        // tf.createEqualityTerm(tf.createVariableTerm(x),
        // tf.createJunctorTerm(Junctor.TRUE));
        // } catch (TermCreationException e) {
        // exc = e;
        // }
        // assertTrue("Expected TermCreationException. But was:" + exc,
        // exc instanceof TermCreationException);
    }

    @Test
    public void testSubSortsSubst() {
        JTerm t = tf.createTerm(g, tf.createTerm(v2), tf.createTerm(v1));
        Function c = new JFunction(new Name("c"), osort2, new Sort[0]);
        JTerm st = TB.subst(WarySubstOp.SUBST, v2, tf.createTerm(c), t);
        c = new JFunction(new Name("c"), osort4, new Sort[0]);
        st = TB.subst(WarySubstOp.SUBST, v2, tf.createTerm(c), t);
        c = new JFunction(new Name("c"), osort3, new Sort[0]);
        st = TB.subst(WarySubstOp.SUBST, v1, tf.createTerm(c), t);
        Exception exc = new Exception();
        try {
            c = new JFunction(new Name("c"), osort1, new Sort[0]);
            st = TB.subst(WarySubstOp.SUBST, v2, tf.createTerm(c), t);
        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
        exc = new Exception();
        try {
            c = new JFunction(new Name("c"), osort3, new Sort[0]);
            st = TB.subst(WarySubstOp.SUBST, v2, tf.createTerm(c), t);

        } catch (TermCreationException e) {
            exc = e;
        }
        assertTrue(exc instanceof TermCreationException);
    }


    /**
     * Tests the caching of {@link JTerm}s with and without {@link JavaBlock}s.
     */
    @Test
    public void testCaching() {
        // Create Terms first time
        JTerm noJB = tf.createTerm(Junctor.TRUE);
        JTerm noJBWithChild = tf.createTerm(Junctor.NOT, noJB);
        JavaBlock javaBlock =
            JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
        JTerm withJB =
            tf.createTerm(JModality.getModality(JModality.JavaModalityKind.DIA, javaBlock),
                new ImmutableArray<>(noJB), null);
        JTerm withJBChild = tf.createTerm(Junctor.NOT, withJB);
        JTerm withJBChildChild = tf.createTerm(Junctor.NOT, withJBChild);
        // Create Same terms again
        JTerm noJBAgain = tf.createTerm(Junctor.TRUE);
        JTerm noJBWithChildAgain = tf.createTerm(Junctor.NOT, noJB);
        JavaBlock javaBlockAgain =
            JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
        JTerm withJBAgain =
            tf.createTerm(JModality.getModality(JModality.JavaModalityKind.DIA, javaBlockAgain),
                new ImmutableArray<>(noJB), null);
        JTerm withJBChildAgain = tf.createTerm(Junctor.NOT, withJB);
        JTerm withJBChildChildAgain = tf.createTerm(Junctor.NOT, withJBChild);
        // Test caching
        assertSame(noJB, noJBAgain);
        assertSame(noJBWithChild, noJBWithChildAgain);
        assertNotSame(withJB, withJBAgain);
        assertNotSame(withJBChild, withJBChildAgain);
        assertNotSame(withJBChildChild, withJBChildChildAgain);
    }
}
