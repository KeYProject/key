/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.equality.RenamingProperty;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


public class TestTerm {

    private TermBuilder tb;
    private TermFactory tf;

    private final Sort sort1 = new SortImpl(new Name("S1"));
    private final Sort sort2 = new SortImpl(new Name("S2"));
    private final Sort sort3 = new SortImpl(new Name("S3"));


    private final JFunction p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, sort1);
    // p(:S1):BOOL
    private final LogicVariable x = new LogicVariable(new Name("x"), sort1); // x:S1
    // q(:Whatever):BOOL
    private final LogicVariable z = new LogicVariable(new Name("z"), sort1); // z:S1
    private final LogicVariable zz = new LogicVariable(new Name("zz"), sort1); // zz:S1
    private final JFunction r =
        new JFunction(new Name("r"), JavaDLTheory.FORMULA, sort1, sort2);
    // r(:S1, :S2):BOOL
    private final LogicVariable y = new LogicVariable(new Name("y"), sort3); // y:S3
    private final LogicVariable w = new LogicVariable(new Name("w"), sort2); // w:S2
    private final JFunction f = new JFunction(new Name("f"), sort1, sort3);
    // f(:S3):S1

    private final ProgramVariable pv0 = new LocationVariable(new ProgramElementName("pv0"), sort1); // pv0:S1

    @BeforeEach
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = tb.tf();
    }

    private Term t1() {
        Term t_x = tf.createTerm(x);
        return tf.createTerm(p, new Term[] { t_x }, null, null);
    }

    private Term t2() {
        Term t_x = tf.createTerm(x);
        Term t_w = tf.createTerm(w);
        return tf.createTerm(r, new Term[] { t_x, t_w }, null, null);
    }

    private Term t3() {
        Term t_y = tf.createTerm(y);
        return tf.createTerm(f, new Term[] { t_y }, null, null);
    }

    private Term t4() {
        Term t_pv0 = tf.createTerm(pv0);
        return tf.createTerm(p, new Term[] { t_pv0 }, null, null);
    }

    @Test
    public void testFreeVars1() {
        Term t_allxt2 = tb.all(x, t2());
        Term t_allxt2_andt1 = tf.createTerm(Junctor.AND, t_allxt2, t1());
        assertTrue(t_allxt2_andt1.freeVars().contains(w) && t_allxt2_andt1.freeVars().contains(x));
    }

    @Test
    public void testFreeVars2() {
        Term t_allxt2 = tb.all(w, t2());
        Term t_allxt2_andt1 = tf.createTerm(Junctor.AND, t_allxt2, t1());
        assertTrue(!t_allxt2_andt1.freeVars().contains(w) && t_allxt2_andt1.freeVars().contains(x));
    }

    @Test
    public void testFreeVars3() {
        Term t_allxt1 = tb.all(x, t2());
        Term t_allxt1_andt2 = tf.createTerm(Junctor.AND, t_allxt1, t1());
        Term t_exw_allxt1_andt2 = tb.ex(w, t_allxt1_andt2);
        assertTrue(!t_exw_allxt1_andt2.freeVars().contains(w)
                && t_exw_allxt1_andt2.freeVars().contains(x));
    }

    @Test
    public void testFreeVars4() {
        Term t_allxt1 = tb.all(x, t2());
        Term t_allxt1_andt2 = tf.createTerm(Junctor.AND, t_allxt1, t1());
        Term t_exw_allxt1_andt2 =
            tb.ex(ImmutableSLList.<QuantifiableVariable>nil().append(w, x), t_allxt1_andt2);
        assertTrue(!t_exw_allxt1_andt2.freeVars().contains(w)
                && !t_exw_allxt1_andt2.freeVars().contains(x));
    }

    @Test
    public void testProgramElementEqualsModRenaming() {
        Term match1 = TacletForTests.parseTerm("\\<{ int i; }\\>true & \\<{ int i; }\\>true");
        Term match2 = TacletForTests.parseTerm("\\<{ int i; }\\>true ");
        assertTrue(
            match1.sub(0).equalsModProperty(match2, RenamingProperty.RENAMING_PROPERTY),
            "Terms should be equalModRenaming (0).");
        assertTrue(
            match1.sub(0).equalsModProperty(match1.sub(1), RenamingProperty.RENAMING_PROPERTY),
            "Terms should be equalModRenaming (1).");
        Term match3 = TacletForTests.parseTerm("\\<{ int j = 0; }\\>true ");
        assertNotEquals(match1, match3, "Terms should not be equal.");

    }

    @Test
    public void testEqualsModRenamingWithLabels() {
        Term match1 = TacletForTests.parseTerm("\\<{ label0:{ label1:{  } } }\\>true");
        Term match2 = TacletForTests.parseTerm("\\<{ label0:{ label1:{  } } }\\>true");
        assertTrue(match1.equalsModProperty(match2, RenamingProperty.RENAMING_PROPERTY),
            "Terms should be equalModRenaming.");
        Term match3 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        Term match4 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int j = 0; } } }\\>true");
        assertTrue(match3.equalsModProperty(match4, RenamingProperty.RENAMING_PROPERTY),
            "Terms should be equalModRenaming.");
        Term match5 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        Term match6 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        assertTrue(match5.equalsModProperty(match6, RenamingProperty.RENAMING_PROPERTY),
            "Terms should be equalModRenaming.");
    }

    @Test
    public void testEqualsModRenaming() {

        final Term px = tf.createTerm(p, new Term[] { tf.createTerm(x) }, null, null);
        final Term quant1 = tb.all(z, tb.all(zz, tb.all(x, px)));

        final Term pz = tf.createTerm(p, new Term[] { tf.createTerm(z) }, null, null);
        final Term quant2 = tb.all(z, tb.all(z, tb.all(z, pz)));

        assertTrue(quant1.equalsModProperty(quant2, RenamingProperty.RENAMING_PROPERTY),
            "Terms " + quant1 + " and " + quant2 + " should be equal mod renaming");

    }

    /*
     * @Test public void testProgramElementEquals() {
     *
     * Term match1 = TacletForTests.parseTerm("<{ int i = 0; }>true "); Term match2 =
     * TacletForTests.parseTerm("<{ int i = 0; }>true "); assertEquals("Terms should be equal.",
     * match1, match2);
     *
     * Term match3 = TacletForTests.parseTerm("<{ int j = 0; }>true ");
     * assertTrue("Terms should not be equal.", !match1.equals(match3));
     *
     * }
     */
    // @Test public void testsimpleUpdate() {
    // Term t1 = TacletForTests.parseTerm("<{int j,k,l;}>{k:=l}"
    // +"{l:=l}{j:=j}<{ int i = 0;k=0; }>true ");
    // Term t2 = TacletForTests.parseTerm("<{int j,l,k;}>{j:=j}"
    // +"{l:=k}{j:=k}{j:=j}{j:=j}<{ int i = 0;l=0; }>true ");
    // assertTrue("Terms should be equalModRenaming and mod \"simple\" updates.",
    // t1.equalsModRenamingModsU(t2));
    // Term t3 = TacletForTests.parseTerm("<{int j,k,l;}>{k:=k}"
    // +"{j:=Z(3(#))}<{ int i = 0; }>true ");
    // Term t4 = TacletForTests.parseTerm("<{int j,l,k;}>{j:=j}"
    // +"{l:=Z(3(#))}{j:=l}<{ int i = 0;l=0; }>true ");
    // assertTrue("Terms should not be equalModRenaming and mod \"simple\" updates.",
    // !t1.equalsModRenamingModsU(t3));
    // assertTrue("Terms should not be equalModRenaming and mod \"simple\" updates.",
    // !t2.equalsModRenamingModsU(t4));
    // }


    @Test
    public void testRigidness0() {
        assertTrue(t1().isRigid(), "Term t1 should be rigid");
        assertTrue(t2().isRigid(), "Term t2 should be rigid");
        assertTrue(t3().isRigid(), "Term t3 should be rigid");
        assertFalse(t4().isRigid(), "Term t4 should not be rigid");
    }

    /**
     * Tests {@link TermImpl#containsJavaBlockRecursive()}.
     */
    @Test
    public void testIsContainsJavaBlockRecursive() {
        Term noJB = tf.createTerm(Junctor.TRUE);
        Term noJBWithChild = tf.createTerm(Junctor.NOT, noJB);
        JavaBlock javaBlock =
            JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
        Term withJB =
            tf.createTerm(Modality.getModality(Modality.JavaModalityKind.DIA, javaBlock),
                new ImmutableArray<>(noJB), null, null);
        Term withJBChild = tf.createTerm(Junctor.NOT, withJB);
        Term withJBChildChild = tf.createTerm(Junctor.NOT, withJBChild);
        assertFalse(noJB.containsJavaBlockRecursive());
        assertFalse(noJBWithChild.containsJavaBlockRecursive());
        assertTrue(withJB.containsJavaBlockRecursive());
        assertTrue(withJBChild.containsJavaBlockRecursive());
        assertTrue(withJBChildChild.containsJavaBlockRecursive());
    }
}
