// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;



public class TestTerm extends TestCase { 

    private static final TermBuilder TB = TermBuilder.DF;
    private static final TermFactory tf=TermFactory.DEFAULT;

    private Sort sort1=new SortImpl(new Name("S1"));
    private Sort sort2=new SortImpl(new Name("S2"));
    private Sort sort3=new SortImpl(new Name("S3"));
    	

    Function p=new Function(new Name("p"),Sort.FORMULA,new Sort[]{sort1});  
        //p(:S1):BOOL
    LogicVariable x=new LogicVariable(new Name("x"),sort1);  //x:S1
    Function q=new Function(new Name("q"),Sort.FORMULA,
			    new Sort[]{new SortImpl(new Name("Whatever"))}); 
        //q(:Whatever):BOOL
    LogicVariable z=new LogicVariable(new Name("z"),sort1); //z:S1
    LogicVariable zz=new LogicVariable(new Name("zz"),sort1); //zz:S1
    Function r=new Function(new Name("r"),Sort.FORMULA,new Sort[]{sort1, sort2});
        //r(:S1, :S2):BOOL
    LogicVariable y=new LogicVariable(new Name("y"),sort3); //y:S3
    LogicVariable w=new LogicVariable(new Name("w"),sort2); //w:S2
    Function f=new Function(new Name("f"),sort1, new Sort[]{sort3}); 
        // f(:S3):S1

    ProgramVariable pv0=new LocationVariable
	( new ProgramElementName ("pv0"), sort1 ); //pv0:S1


    public TestTerm(String name) {
	super(name);
    }

    private Term t1(){
	Term t_x=tf.createTerm(x);
	Term t_px=tf.createTerm(p, new Term[]{t_x}, null, null);
	return t_px;
    }
  
    private Term t2(){
	Term t_x=tf.createTerm(x);
	Term t_w=tf.createTerm(w);
	return tf.createTerm(r, new Term[]{t_x,t_w}, null, null);
    }

    private Term t3() {
	Term t_y=tf.createTerm(y);
	return tf.createTerm(f, new Term[]{t_y}, null, null);
    }

    private Term t4(){
	Term t_pv0=tf.createTerm(pv0);
	Term t_ppv0=tf.createTerm(p, new Term[]{t_pv0}, null, null);
	return t_ppv0;
    }
  
    public void testFreeVars1() {
	Term t_allxt2=TB.all(x,t2());
	Term t_allxt2_andt1=tf.createTerm(Junctor.AND,t_allxt2,t1());
	assertTrue(t_allxt2_andt1.freeVars().contains(w) 
		   && t_allxt2_andt1.freeVars().contains(x));
    }

   public void testFreeVars2() {
	Term t_allxt2=TB.all(w ,t2());
	Term t_allxt2_andt1=tf.createTerm(Junctor.AND,t_allxt2,t1());
	assertTrue(!t_allxt2_andt1.freeVars().contains(w) 
		   && t_allxt2_andt1.freeVars().contains(x));
    }
    
    public void testFreeVars3() {
	Term t_allxt1=TB.all(x, t2());
	Term t_allxt1_andt2=tf.createTerm(Junctor.AND,t_allxt1,t1());
	Term t_exw_allxt1_andt2=TB.ex(w, t_allxt1_andt2); 
	assertTrue(!t_exw_allxt1_andt2.freeVars().contains(w) 
		   && t_exw_allxt1_andt2.freeVars().contains(x));
    }

   public void testFreeVars4() {
	Term t_allxt1=TB.all(x, t2());
	Term t_allxt1_andt2=tf.createTerm(Junctor.AND,t_allxt1,t1());
	Term t_exw_allxt1_andt2 =
                TB.ex(ImmutableSLList.<QuantifiableVariable>nil().append(w, x),
                     t_allxt1_andt2);
	assertTrue(!t_exw_allxt1_andt2.freeVars().contains(w)
		   && !t_exw_allxt1_andt2.freeVars().contains(x));
    }

    public void testProgramElementEqualsModRenaming() {

	Term match1 = TacletForTests.parseTerm("\\<{ int i; }\\>true & \\<{ int i; }\\>true");
	Term match2 = TacletForTests.parseTerm("\\<{ int i; }\\>true ");
	assertTrue("Terms should be equalModRenaming (0).", match1.sub(0).equalsModRenaming(match2));
	assertTrue("Terms should be equalModRenaming (1).", match1.sub(0).equalsModRenaming(match1.sub(1)));
	Term match3 = TacletForTests.parseTerm("\\<{ int j = 0; }\\>true ");
	assertTrue("Terms should not be equal.", !match1.equals(match3));

    }
    
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

    public void testEqualsModRenaming() {
        
        final Term px = tf.createTerm ( p, new Term[]{tf.createTerm(x)}, null, null );
        final Term quant1 = TB.all(z, TB.all( zz, TB.all( x, px ) ) );
        
        final Term pz = tf.createTerm ( p, new Term[]{tf.createTerm(z)}, null, null );
        final Term quant2 = TB.all(z,
                               TB.all( z,
                                  TB.all( z, pz ) ) );
        
        assertTrue ( "Terms " + quant1 + " and " + quant2
                     + " should be equal mod renaming",
                     quant1.equalsModRenaming ( quant2 ) );
        
    }
    
/*   public void testProgramElementEquals() {

	Term match1 = TacletForTests.parseTerm("<{ int i = 0; }>true ");
	Term match2 = TacletForTests.parseTerm("<{ int i = 0; }>true ");
	assertEquals("Terms should be equal.", match1, match2);

	Term match3 = TacletForTests.parseTerm("<{ int j = 0; }>true ");
	assertTrue("Terms should not be equal.", !match1.equals(match3));

    }
*/
//     public void testsimpleUpdate() {
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



    public void testRigidness0 () {
	assertTrue ( "Term t1 should be rigid",
		     t1 ().isRigid () );
	assertTrue ( "Term t2 should be rigid",
		     t2 ().isRigid () );
	assertTrue ( "Term t3 should be rigid",
		     t3 ().isRigid () );
	assertFalse ( "Term t4 should not be rigid",
		      t4 ().isRigid () );
    }

   /**
    * Tests {@link TermImpl#isContainsJavaBlockRecursive()}.
    */
   public void testIsContainsJavaBlockRecursive() {
      Term noJB = tf.createTerm(Junctor.TRUE);
      Term noJBWithChild = tf.createTerm(Junctor.NOT, noJB);
      JavaBlock javaBlock = JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
      Term withJB = tf.createTerm(Modality.DIA, new ImmutableArray<Term>(noJB), null, javaBlock);
      Term withJBChild = tf.createTerm(Junctor.NOT, withJB);
      Term withJBChildChild = tf.createTerm(Junctor.NOT, withJBChild);
      assertFalse(noJB.isContainsJavaBlockRecursive());
      assertFalse(noJBWithChild.isContainsJavaBlockRecursive());
      assertTrue(withJB.isContainsJavaBlockRecursive());
      assertTrue(withJBChild.isContainsJavaBlockRecursive());
      assertTrue(withJBChildChild.isContainsJavaBlockRecursive());
   }
}
