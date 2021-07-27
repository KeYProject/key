// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;

import static org.junit.Assert.*;


public class TestTerm {

    private TermBuilder tb;
    private TermFactory tf;

    private final Sort sort1 = new SortImpl(new Name("S1"));
    private final Sort sort2 = new SortImpl(new Name("S2"));
    private final Sort sort3 = new SortImpl(new Name("S3"));


    private final Function p = new Function(new Name("p"), Sort.FORMULA, sort1);
    //p(:S1):BOOL
    private final LogicVariable x = new LogicVariable(new Name("x"), sort1);  //x:S1
    //q(:Whatever):BOOL
    private final LogicVariable z = new LogicVariable(new Name("z"), sort1); //z:S1
    private final LogicVariable zz = new LogicVariable(new Name("zz"), sort1); //zz:S1
    private final Function r = new Function(new Name("r"), Sort.FORMULA, sort1, sort2);
    //r(:S1, :S2):BOOL
    private final LogicVariable y = new LogicVariable(new Name("y"), sort3); //y:S3
    private final LogicVariable w = new LogicVariable(new Name("w"), sort2); //w:S2
    private final Function f = new Function(new Name("f"), sort1, sort3);
    // f(:S3):S1

    private final ProgramVariable pv0 = new LocationVariable(new ProgramElementName("pv0"), sort1); //pv0:S1

    @Before
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = tb.tf();
    }

    private Term t1() {
        Term t_x = tf.createTerm(x);
        return tf.createTerm(p, new Term[]{t_x}, null, null);
    }

    private Term t2() {
        Term t_x = tf.createTerm(x);
        Term t_w = tf.createTerm(w);
        return tf.createTerm(r, new Term[]{t_x, t_w}, null, null);
    }

    private Term t3() {
        Term t_y = tf.createTerm(y);
        return tf.createTerm(f, new Term[]{t_y}, null, null);
    }

    private Term t4() {
        Term t_pv0 = tf.createTerm(pv0);
        return tf.createTerm(p, new Term[]{t_pv0}, null, null);
    }

    @Test
    public void testFreeVars1() {
        Term t_allxt2 = tb.all(x, t2());
        Term t_allxt2_andt1 = tf.createTerm(Junctor.AND, t_allxt2, t1());
        assertTrue(t_allxt2_andt1.freeVars().contains(w)
                && t_allxt2_andt1.freeVars().contains(x));
    }

    @Test
    public void testFreeVars2() {
        Term t_allxt2 = tb.all(w, t2());
        Term t_allxt2_andt1 = tf.createTerm(Junctor.AND, t_allxt2, t1());
        assertTrue(!t_allxt2_andt1.freeVars().contains(w)
                && t_allxt2_andt1.freeVars().contains(x));
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
                tb.ex(ImmutableSLList.<QuantifiableVariable>nil().append(w, x),
                        t_allxt1_andt2);
        assertTrue(!t_exw_allxt1_andt2.freeVars().contains(w)
                && !t_exw_allxt1_andt2.freeVars().contains(x));
    }

    @Test
    public void testProgramElementEqualsModRenaming() {
        Term match1 = TacletForTests.parseTerm("\\<{ int i; }\\>true & \\<{ int i; }\\>true");
        Term match2 = TacletForTests.parseTerm("\\<{ int i; }\\>true ");
        assertTrue("Terms should be equalModRenaming (0).", match1.sub(0).equalsModRenaming(match2));
        assertTrue("Terms should be equalModRenaming (1).", match1.sub(0).equalsModRenaming(match1.sub(1)));
        Term match3 = TacletForTests.parseTerm("\\<{ int j = 0; }\\>true ");
        assertNotEquals("Terms should not be equal.", match1, match3);

    }

    @Test
    public void testEqualsModRenamingWithLabels() {
        Term match1 = TacletForTests.parseTerm("\\<{ label0:{ label1:{  } } }\\>true");
        Term match2 = TacletForTests.parseTerm("\\<{ label0:{ label1:{  } } }\\>true");
        assertTrue("Terms should be equalModRenaming.", match1.equalsModRenaming(match2));
        Term match3 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        Term match4 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int j = 0; } } }\\>true");
        assertTrue("Terms should be equalModRenaming.", match3.equalsModRenaming(match4));
        Term match5 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        Term match6 = TacletForTests.parseTerm("\\<{ label0:{ label1:{ int i = 0; } } }\\>true");
        assertTrue("Terms should be equalModRenaming.", match5.equalsModRenaming(match6));
    }

    @Test
    public void testEqualsModRenaming() {

        final Term px = tf.createTerm(p, new Term[]{tf.createTerm(x)}, null, null);
        final Term quant1 = tb.all(z, tb.all(zz, tb.all(x, px)));

        final Term pz = tf.createTerm(p, new Term[]{tf.createTerm(z)}, null, null);
        final Term quant2 = tb.all(z,
                tb.all(z,
                        tb.all(z, pz)));

        assertTrue("Terms " + quant1 + " and " + quant2
                        + " should be equal mod renaming",
                quant1.equalsModRenaming(quant2));

    }
    
/*   @Test public void testProgramElementEquals() {

	Term match1 = TacletForTests.parseTerm("<{ int i = 0; }>true ");
	Term match2 = TacletForTests.parseTerm("<{ int i = 0; }>true ");
	assertEquals("Terms should be equal.", match1, match2);

	Term match3 = TacletForTests.parseTerm("<{ int j = 0; }>true ");
	assertTrue("Terms should not be equal.", !match1.equals(match3));

    }
*/
//     @Test public void testsimpleUpdate() {
// 	  Term t1 = TacletForTests.parseTerm("<{int j,k,l;}>{k:=l}"
//                                     +"{l:=l}{j:=j}<{ int i = 0;k=0; }>true ");
// 	  Term t2 = TacletForTests.parseTerm("<{int j,l,k;}>{j:=j}"
//                 +"{l:=k}{j:=k}{j:=j}{j:=j}<{ int i = 0;l=0; }>true ");
// 	  assertTrue("Terms should be equalModRenaming and mod \"simple\" updates.",
// 		     t1.equalsModRenamingModsU(t2));
// 	  Term t3 = TacletForTests.parseTerm("<{int j,k,l;}>{k:=k}"
//                                     +"{j:=Z(3(#))}<{ int i = 0; }>true ");
// 	  Term t4 = TacletForTests.parseTerm("<{int j,l,k;}>{j:=j}"
//                               +"{l:=Z(3(#))}{j:=l}<{ int i = 0;l=0; }>true ");
// 	  assertTrue("Terms should not be equalModRenaming and mod \"simple\" updates.",
// 		     !t1.equalsModRenamingModsU(t3));
// 	  assertTrue("Terms should not be equalModRenaming and mod \"simple\" updates.",
// 		     !t2.equalsModRenamingModsU(t4));
//     }


    @Test
    public void testRigidness0() {
        assertTrue("Term t1 should be rigid",
                t1().isRigid());
        assertTrue("Term t2 should be rigid",
                t2().isRigid());
        assertTrue("Term t3 should be rigid",
                t3().isRigid());
        assertFalse("Term t4 should not be rigid",
                t4().isRigid());
    }

    /**
     * Tests {@link TermImpl#containsJavaBlockRecursive()}.
     */
    @Test
    public void testIsContainsJavaBlockRecursive() {
        Term noJB = tf.createTerm(Junctor.TRUE);
        Term noJBWithChild = tf.createTerm(Junctor.NOT, noJB);
        JavaBlock javaBlock = JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
        Term withJB = tf.createTerm(Modality.DIA, new ImmutableArray<>(noJB), null, javaBlock);
        Term withJBChild = tf.createTerm(Junctor.NOT, withJB);
        Term withJBChildChild = tf.createTerm(Junctor.NOT, withJBChild);
        assertFalse(noJB.containsJavaBlockRecursive());
        assertFalse(noJBWithChild.containsJavaBlockRecursive());
        assertTrue(withJB.containsJavaBlockRecursive());
        assertTrue(withJBChild.containsJavaBlockRecursive());
        assertTrue(withJBChildChild.containsJavaBlockRecursive());
    }
}