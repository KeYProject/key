// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ClassInstanceSortImpl;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
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
						  DefaultImmutableSet.<Sort>nil()
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
	Term et_x=OpTerm.createOpTerm(x, new Term[0]);
	Term et_px=OpTerm.createOpTerm(p, new Term[]{et_x});
	et1=et_px;       
    }

    private ProgramVariable attribute(Term t) {
	return (ProgramVariable)((AttributeOp)t.op()).attribute();
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

	Exception exc=new Exception();
	try {
	    Term t_x=tf.createFunctionTerm(x, new Term[0]);
	    Term t_rx=tf.createFunctionTerm(r, new Term[]{t_x});
	} catch (TermCreationException e) {
	    exc=e;	   
	}
	assertTrue(exc instanceof TermCreationException);
    }

    /**
     * subformulae are invalid built, but the term shall be
     * constructed anyway, as subformulae are not checked
     */
    public void testWithInvalidSubformulae() { 
	Term invalidBuilt=OpTerm.createOpTerm(p, new Term[]{ OpTerm.createOpTerm(y, new Term[0])});
	try {
	    Term t_px_or_py=tf.createJunctorTerm(Op.OR,
						 new Term[]{invalidBuilt, 
							    t1()});
	} catch (Exception e) {
	    fail();
	}
    }  

    public void testConstantTrue() {
        Term t_true=tf.createJunctorTerm(Op.TRUE,new Term[0]);
	Assert.assertEquals(t_true,OpTerm.createOpTerm(Op.TRUE, new Term[0]));
    }

    public void testQuantifierTerm() {
	Term t_forallx_px=tf.createQuantifierTerm(Op.ALL,
						  new LogicVariable[]{x},t1());
	Assert.assertEquals(t_forallx_px,
			    new QuantifierTerm(Op.ALL,new LogicVariable[]{x},t1()));
    }

    public void testJunctorTerm() {
	Term  t_px_imp_ryw= tf.createJunctorTerm(Op.IMP, t1(), t2());
	Assert.assertEquals(t_px_imp_ryw, OpTerm.createOpTerm(Op.IMP, new Term[]{ t1(), t2()}));
    }

    public void testNegationTerm() {
	Term t_not_ryw=tf.createJunctorTerm(Op.NOT, t2());
	Assert.assertEquals(t_not_ryw, OpTerm.createOpTerm(Op.NOT, new Term[]{ t2()}));
    }

    public void testDiamondTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createDiamondTerm(jb, t2());
	Assert.assertEquals(t_dia_ryw, new ProgramTerm(Op.DIA, jb, t2()));
    }

    public void testBoxTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createBoxTerm(jb, t2());
	Assert.assertEquals(t_dia_ryw, new ProgramTerm(Op.BOX, jb, t2()));
    }

    public void testSubstitutionTerm() {
	Term t_x_subst_fy_in_px=tf.createSubstitutionTerm(Op.SUBST, x, t3(),
							  t1());
	Assert.assertEquals(t_x_subst_fy_in_px, 
			    new SubstitutionTerm(Op.SUBST,
						 x, new Term[]{ t3(),t1() }));
    }


    public void testWrongSubstTermForLogicVariable(){
	Exception exc=new Exception();
	try {
	    Term t_x_subst_fy_in_px=tf.createSubstitutionTerm(Op.SUBST, 
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
	    tf.createQuantifierTerm(Op.ALL,new LogicVariable[]{}, t1());
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }
    

    public void testJunctorTermWithWrongArity() {
	Exception exc=new Exception();
	try {
	    tf.createJunctorTerm(Op.NOT,new Term[] {t1(), t2()});
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
			    OpTerm.createOpTerm(p, new Term[]{
					       OpTerm.createOpTerm(xx, new Term[0])}));
    }


    public void testAttributeTerm() {
	Sort s_int = new PrimitiveSort(new Name("int"));
	ProgramVariable attribute = new LocationVariable(new ProgramElementName("size"), 
							new KeYJavaType(s_int));
	Sort s_list = new ClassInstanceSortImpl(new Name("list"), osort4, false);
	ProgramVariable prefix 
	    = new LocationVariable(new ProgramElementName("persons"), 
				  new KeYJavaType(s_list));
	Term sub = tf.createVariableTerm(prefix);
	Term t = tf.createAttributeTerm(attribute, sub);
	assertTrue("Operator should be of type AttributeOp", 
	       t.op() instanceof AttributeOp); 
	assertSame("Sub term should be "+sub+" but is "+t.sub(0), 
		   t.sub(0), sub); 
	assertSame("Wrong attribute.",
		   attribute(t), attribute); 
	prefix = new LocationVariable(new ProgramElementName("persons"), 
				     new KeYJavaType(osort3));
	sub = tf.createVariableTerm(prefix);
	t = tf.createAttributeTerm(attribute, sub);
	Exception exc=new Exception();
	try {
	    prefix = new LocationVariable(new ProgramElementName("persons"), 
					 new KeYJavaType(osort1));
	    sub = tf.createVariableTerm(prefix);
	    t = tf.createAttributeTerm(attribute, sub);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	exc=new Exception();
	try {
	    prefix = new LocationVariable(new ProgramElementName("persons"), 
					 new KeYJavaType(s_int));
	    sub = tf.createVariableTerm(prefix);
	    t = tf.createAttributeTerm(attribute, sub);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	

// 	de.uka.ilkd.key.gui.PureSequentPrinter pseq = 
// 	    new de.uka.ilkd.key.gui.PureSequentPrinter
// 	    (null, new de.uka.ilkd.key.gui.NotationInfo(),
// 	     Sequent.createAnteSequent
// 	     (Semisequent.EMPTY_SEMISEQUENT.insertFirst(new ConstrainedFormula
// 							(tf.createEqualityTerm(t,t)))));
// 	pseq.printSequent();
// 	System.out.println("Prettyprint:"+pseq);
// 	System.out.println("toString:"+t);
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
	Exception exc=new Exception();
	try {
	    tf.createEqualityTerm(tf.createVariableTerm(v1), 
				  tf.createVariableTerm(y));
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc = null;
	try {
	    tf.createEqualityTerm(tf.createVariableTerm(x), 
				  tf.createJunctorTerm(Op.TRUE));
	} catch (TermCreationException e) {
	    exc = e;	    
	}
	assertTrue("Expected TermCreationException. But was:" +exc, exc instanceof TermCreationException);
    }

    public void testSubSortsSubst() {
	Term t = tf.createFunctionTerm(g, tf.createVariableTerm(v2), 
				       tf.createVariableTerm(v1));
	Function c=new RigidFunction(new Name("c"), osort2, new Sort[0]);
	Term st = tf.createSubstitutionTerm(Op.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	c=new RigidFunction(new Name("c"), osort4, new Sort[0]);
	st = tf.createSubstitutionTerm(Op.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	c=new RigidFunction(new Name("c"), osort3, new Sort[0]);
	st = tf.createSubstitutionTerm(Op.SUBST, v1, 
					    tf.createFunctionTerm(c), t);
	Exception exc=new Exception();
	try {
	    c=new RigidFunction(new Name("c"), osort1, new Sort[0]);
	    st = tf.createSubstitutionTerm(Op.SUBST, v2, 
					    tf.createFunctionTerm(c), t);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc=new Exception();
	try {
	    c=new RigidFunction(new Name("c"), osort3, new Sort[0]);
	    st = tf.createSubstitutionTerm(Op.SUBST, v2, 
					   tf.createFunctionTerm(c), t);
	    
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }


}
