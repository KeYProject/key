// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import junit.framework.Assert;
import junit.framework.TestCase;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ClassInstanceSortImpl;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/** class tests the term factory
*/
public class TestTermFactory extends TestCase { 
    

    private static final TermFactory tf = TermFactory.DEFAULT;
    private Term et1;
    private Sort sort1=new PrimitiveSort(new Name("S1"));
    private Sort sort2=new PrimitiveSort(new Name("S2"));
    private Sort sort3=new PrimitiveSort(new Name("S3"));
    private Sort osort1=new ClassInstanceSortImpl(new Name("os1"), false);
    private Sort osort2=new ClassInstanceSortImpl(new Name("os2"), osort1, false);
    private Sort osort3=new ClassInstanceSortImpl(new Name("os3"), osort1, false);
    private Sort osort4=new ClassInstanceSortImpl(new Name("os4"), 
						  SetAsListOfSort.EMPTY_SET
						  .add(osort2).add(osort3), false);
    
    Function p=new RigidFunction(new Name("p"),Sort.FORMULA,new Sort[]{sort1});  
        //p(:S1):BOOL
    LogicVariable x=new LogicVariable(new Name("x"),sort1);  //x:S1
    Function q=new RigidFunction(new Name("q"),Sort.FORMULA,
			    new Sort[]{new PrimitiveSort(new Name("Whatever"))}); 
        //q(:Whatever):BOOL
    LogicVariable z=new LogicVariable(new Name("z"),sort1); //z:S1
    Function r=new RigidFunction(new Name("r"),Sort.FORMULA,new Sort[]{sort1, sort2});
        //r(:S1, :S2):BOOL
    LogicVariable y=new LogicVariable(new Name("y"),sort3); //y:S3
    LogicVariable w=new LogicVariable(new Name("w"),sort2); //w:S2
    Function f=new RigidFunction(new Name("f"),sort1, new Sort[]{sort3}); 
        // f(:S3):S1

    LogicVariable v1=new LogicVariable(new Name("v1"), osort1);
    LogicVariable v2=new LogicVariable(new Name("v2"), osort2);
    LogicVariable v3=new LogicVariable(new Name("v3"), osort3);
    LogicVariable v4=new LogicVariable(new Name("v4"), osort4);

    Function g=new RigidFunction(new Name("g"), osort3, new Sort[]{osort2, osort1});

    public TestTermFactory(String name) {
	super(name);
    }

    public void setUp() {
	Term et_x=new TermImpl(x, new Term[0]);
	Term et_px=new TermImpl(p, new Term[]{et_x});
	et1=et_px;       
    }

    private Term t1(){
	Term t_x=tf.createFunctionTerm(x, new Term[0]);
	Term t_px=tf.createFunctionTerm(p, new Term[]{t_x});
	return t_px;
    }
  
    private Term t2(){
	Term t_x=tf.createFunctionTerm(x, new Term[]{});
	Term t_w=tf.createFunctionTerm(w, new Term[]{});
	return tf.createFunctionTerm(r, new Term[]{t_x,t_w});
    }

    private Term t3() {
	Term t_y=tf.createFunctionTerm(y, new Term[]{});
	return tf.createFunctionTerm(f, new Term[]{t_y});
    }


    public void testWrongSorts() {
      
	Exception exc=new Exception();
	try {
	    Term t_z  = tf.createFunctionTerm(z, new Term[0]);
	    Term t_pz = tf.createFunctionTerm(q, new Term[]{t_z});
	} catch (TermCreationException e) {
	    exc=e;
	    
	}
	assertTrue(exc instanceof TermCreationException);
    }
    
    public void testSimplePredicate() {
	Assert.assertEquals(t1(),et1);
    }

    public void testWrongArity() {

	Exception exc = null;
	try {
	    Term t_x=tf.createFunctionTerm(x, new Term[0]);
	    tf.createFunctionTerm(r, new Term[]{t_x});
	} catch (TermCreationException e) {
	    exc=e;	   
	}
	assertTrue("expected TermCreationException but got " + exc,
		   exc instanceof TermCreationException);
    }

    /**
     * subformulae are invalid built, but the term shall be
     * constructed anyway, as subformulae are not checked
     */
    public void testWithInvalidSubformulae() { 
	Term invalidBuilt=new TermImpl(p, new Term[]{ new TermImpl(y, new Term[0])});
	try {
	    Term t_px_or_py=tf.createJunctorTerm(Junctor.OR,
						 new Term[]{invalidBuilt, 
							    t1()});
	} catch (Exception e) {
	    fail();
	}
    }  

    public void testConstantTrue() {
        Term t_true=tf.createJunctorTerm(Junctor.TRUE,new Term[0]);
	Assert.assertEquals(t_true,new TermImpl(Junctor.TRUE, new Term[0]));
    }

    public void testQuantifierTerm() {
	Term t_forallx_px=tf.createQuantifierTerm(Quantifier.ALL,
						  new LogicVariable[]{x},t1());
	Assert.assertEquals(t_forallx_px,
			    new TermImpl(Quantifier.ALL,new ArrayOfTerm(t1()), null, new ArrayOfQuantifiableVariable(x)));
    }

    public void testJunctorTerm() {
	Term  t_px_imp_ryw= tf.createJunctorTerm(Junctor.IMP, t1(), t2());
	Assert.assertEquals(t_px_imp_ryw, new TermImpl(Junctor.IMP, new Term[]{ t1(), t2()}));
    }

    public void testNegationTerm() {
	Term t_not_ryw=tf.createJunctorTerm(Junctor.NOT, t2());
	Assert.assertEquals(t_not_ryw, new TermImpl(Junctor.NOT, new Term[]{ t2()}));
    }

    public void testDiamondTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createDiamondTerm(jb, t2());
	Assert.assertEquals(t_dia_ryw, new TermImpl(Modality.DIA, new ArrayOfTerm(t2()), jb));
    }

    public void testBoxTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createBoxTerm(jb, t2());
	Assert.assertEquals(t_dia_ryw, new TermImpl(Modality.BOX, new ArrayOfTerm(t2()), jb));
    }

    public void testSubstitutionTerm() {
	Term t_x_subst_fy_in_px=tf.createSubstitutionTerm(WarySubstOp.SUBST, x, t3(),
							  t1());
	Assert.assertEquals(new TermImpl(WarySubstOp.SUBST, new ArrayOfTerm(new Term[]{ t3(),t1() }),
				    	 null, new ArrayOfQuantifiableVariable[]{new ArrayOfQuantifiableVariable(),
	                                                                         new ArrayOfQuantifiableVariable(x)}), 
			    t_x_subst_fy_in_px);
    }


    public void testWrongSubstTermForLogicVariable(){
	Exception exc=new Exception();
	try {
	    tf.createSubstitutionTerm(WarySubstOp.SUBST, 
							      x, new Term[]{ t2(), t1()});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    public void testSubtermsForLogicVariable() {
	Exception exc=new Exception();
	try {
	    tf.createFunctionTerm(x,new Term[]{t3()});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException );
    }    
    

    public void testQuantifierWithNoBoundSubTerms() {
	Exception exc=new Exception();
	try {
	    tf.createQuantifierTerm(Quantifier.ALL,new LogicVariable[]{}, t1());
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }
    

    public void testJunctorTermWithWrongArity() {
	Exception exc=new Exception();
	try {
	    tf.createJunctorTerm(Junctor.NOT,new Term[] {t1(), t2()});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    public void testMetavariable() {
	Metavariable xx=new Metavariable(new Name("xx"),sort1);
	Term t_mv=tf.createFunctionTerm(xx, new Term[0]);
	Term t_pxx=tf.createFunctionTerm(p, new Term[]{t_mv});	
	Assert.assertEquals(t_pxx,
			    new TermImpl(p, new Term[]{
					       new TermImpl(xx, new Term[0])}));
    }


    public void testSubSorts1() {
	tf.createFunctionTerm(g, tf.createVariableTerm(v4), 
			      tf.createVariableTerm(v1));
	tf.createFunctionTerm(g, tf.createVariableTerm(v4), 
			      tf.createVariableTerm(v4));
	tf.createFunctionTerm(g, tf.createVariableTerm(v2), 
			      tf.createVariableTerm(v3));
	Exception exc=new Exception();
	try {
	    tf.createFunctionTerm(g, tf.createVariableTerm(v1), 
				  tf.createVariableTerm(v1));
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc=new Exception();
	try {
	    tf.createFunctionTerm(g, tf.createVariableTerm(y), 
				  tf.createVariableTerm(y));
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    public void testSubSortsEquals() {
	tf.createEqualityTerm(tf.createVariableTerm(v4), 
			      tf.createVariableTerm(v1));
	tf.createEqualityTerm(tf.createVariableTerm(v4), 
			      tf.createVariableTerm(v4));
	tf.createEqualityTerm(tf.createVariableTerm(v2), 
			      tf.createVariableTerm(v3));
	tf.createEqualityTerm(tf.createVariableTerm(x), 
			      tf.createVariableTerm(z));
	Exception exc = null;
//	try { XXX
//	    tf.createEqualityTerm(tf.createVariableTerm(v1), 
//				  TermBuilder.DF.skip());
//	} catch (TermCreationException e) {
//	    exc=e;	    
//	}
//	assertTrue("Expected TermCreationException. But was:" + exc, 
//		   exc instanceof TermCreationException);
//	exc = null;
//	try {
//	    tf.createEqualityTerm(tf.createVariableTerm(x), 
//				  tf.createJunctorTerm(Junctor.TRUE));
//	} catch (TermCreationException e) {
//	    exc = e;	    
//	}
//	assertTrue("Expected TermCreationException. But was:" + exc, 
//		   exc instanceof TermCreationException);
    }

    public void testSubSortsSubst() {
	Term t = tf.createFunctionTerm(g, tf.createVariableTerm(v2), 
				       tf.createVariableTerm(v1));
	Function c=new RigidFunction(new Name("c"), osort2, new Sort[0]);
	Term st = tf.createSubstitutionTerm(WarySubstOp.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	c=new RigidFunction(new Name("c"), osort4, new Sort[0]);
	st = tf.createSubstitutionTerm(WarySubstOp.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	c=new RigidFunction(new Name("c"), osort3, new Sort[0]);
	st = tf.createSubstitutionTerm(WarySubstOp.SUBST, v1, 
					    tf.createFunctionTerm(c), t);
	Exception exc=new Exception();
	try {
	    c=new RigidFunction(new Name("c"), osort1, new Sort[0]);
	    st = tf.createSubstitutionTerm(WarySubstOp.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc=new Exception();
	try {
	    c=new RigidFunction(new Name("c"), osort3, new Sort[0]);
	    st = tf.createSubstitutionTerm(WarySubstOp.SUBST, v2, 
					   tf.createFunctionTerm(c), t);
	    
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }


}
