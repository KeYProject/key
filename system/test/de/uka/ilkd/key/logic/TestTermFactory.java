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

import junit.framework.Assert;
import junit.framework.TestCase;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

/** class tests the term factory
*/
public class TestTermFactory extends TestCase {
    

    private static final TermFactory tf = TermFactory.DEFAULT;
    private Term et1;
    private Sort sort1  = new SortImpl(new Name("S1"));
    private Sort sort2  = new SortImpl(new Name("S2"));
    private Sort sort3  = new SortImpl(new Name("S3"));
    private Sort osort1 = new SortImpl(new Name("os1"));
    private Sort osort2 = new SortImpl(new Name("os2"), osort1);
    private Sort osort3 = new SortImpl(new Name("os3"), osort1);
    private Sort osort4 = new SortImpl(new Name("os4"), 
						  DefaultImmutableSet.<Sort>nil()
						  .add(osort2).add(osort3), false);
    
    Function p=new Function(new Name("p"),Sort.FORMULA,new Sort[]{sort1});  
        //p(:S1):BOOL
    LogicVariable x=new LogicVariable(new Name("x"),sort1);  //x:S1
    Function q=new Function(new Name("q"),Sort.FORMULA,
			    new Sort[]{new SortImpl(new Name("Whatever"))}); 
        //q(:Whatever):BOOL
    LogicVariable z=new LogicVariable(new Name("z"),sort1); //z:S1
    Function r=new Function(new Name("r"),Sort.FORMULA,new Sort[]{sort1, sort2});
        //r(:S1, :S2):BOOL
    LogicVariable y=new LogicVariable(new Name("y"),sort3); //y:S3
    LogicVariable w=new LogicVariable(new Name("w"),sort2); //w:S2
    Function f=new Function(new Name("f"),sort1, new Sort[]{sort3}); 
        // f(:S3):S1

    LogicVariable v1=new LogicVariable(new Name("v1"), osort1);
    LogicVariable v2=new LogicVariable(new Name("v2"), osort2);
    LogicVariable v3=new LogicVariable(new Name("v3"), osort3);
    LogicVariable v4=new LogicVariable(new Name("v4"), osort4);

    Function g=new Function(new Name("g"), osort3, new Sort[]{osort2, osort1});

    public TestTermFactory(String name) {
	super(name);
    }

    public void setUp() {
	Term et_x=new TermImpl(x, new ImmutableArray<Term>(), null, null);
	Term et_px=new TermImpl(p, new ImmutableArray<Term>(new Term[]{et_x}), null, null);
	et1=et_px;       
    }

    private Term t1(){
	Term t_x=tf.createTerm(x, new Term[0]);
	Term t_px=tf.createTerm(p, new Term[]{t_x});
	return t_px;
    }
  
    private Term t2(){
	Term t_x=tf.createTerm(x, new Term[]{});
	Term t_w=tf.createTerm(w, new Term[]{});
	return tf.createTerm(r, new Term[]{t_x,t_w});
    }

    private Term t3() {
	Term t_y=tf.createTerm(y, new Term[]{});
	return tf.createTerm(f, new Term[]{t_y});
    }


    public void testWrongSorts() {
      
	Exception exc=new Exception();
	try {
	    Term t_z  = tf.createTerm(z, new Term[0]);
	    Term t_pz = tf.createTerm(q, new Term[]{t_z});
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
	    Term t_x=tf.createTerm(x, new Term[0]);
	    tf.createTerm(r, new Term[]{t_x});
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
	Term invalidBuilt=new TermImpl(p, new ImmutableArray<Term>(new TermImpl(y, new ImmutableArray<Term>(), null, null)), null, null);
	try {
	    Term t_px_or_py=tf.createTerm(Junctor.OR,
						 new Term[]{invalidBuilt, 
							    t1()});
	} catch (Exception e) {
	    fail();
	}
    }  

    public void testConstantTrue() {
        Term t_true=tf.createTerm(Junctor.TRUE);
	Assert.assertEquals(t_true,new TermImpl(Junctor.TRUE, new ImmutableArray<Term>(), null, null));
    }

    public void testQuantifierTerm() {
	Term t_forallx_px=TermBuilder.DF.all(ImmutableSLList.<QuantifiableVariable>nil().append(x),t1());
	Assert.assertEquals(t_forallx_px,
			    new TermImpl(Quantifier.ALL,new ImmutableArray<Term>(t1()), new ImmutableArray<QuantifiableVariable>(x), null));
    }

    public void testJunctorTerm() {
	Term  t_px_imp_ryw= tf.createTerm(Junctor.IMP, t1(), t2());
	Assert.assertEquals(t_px_imp_ryw, new TermImpl(Junctor.IMP, new ImmutableArray<Term>(new Term[]{ t1(), t2()}), null, null));
    }

    public void testNegationTerm() {
	Term t_not_ryw=tf.createTerm(Junctor.NOT, t2());
	Assert.assertEquals(t_not_ryw, new TermImpl(Junctor.NOT, new ImmutableArray<Term>( t2()), null, null));
    }

    public void testDiamondTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createTerm(Modality.DIA, new Term[]{t2()}, null, jb);
	Assert.assertEquals(t_dia_ryw, new TermImpl(Modality.DIA, new ImmutableArray<Term>(t2()), null, jb));
    }

    public void testBoxTerm() {
	JavaBlock jb=JavaBlock.EMPTY_JAVABLOCK;
	Term t_dia_ryw=tf.createTerm(Modality.BOX, new ImmutableArray<Term>(t2()), null, jb);
	Assert.assertEquals(t_dia_ryw, new TermImpl(Modality.BOX, new ImmutableArray<Term>(t2()), null, jb));
    }

    public void testSubstitutionTerm() {
	Term t_x_subst_fy_in_px=TermBuilder.DF.subst(WarySubstOp.SUBST, x, t3(),
							  t1());
	Assert.assertEquals(new TermImpl(WarySubstOp.SUBST, new ImmutableArray<Term>(new Term[]{ t3(),t1() }),
				    	 new ImmutableArray<QuantifiableVariable>(x), null), 
			    t_x_subst_fy_in_px);
    }


    public void testWrongSubstTermForLogicVariable(){
	Exception exc=new Exception();
	try {
	    tf.createTerm(WarySubstOp.SUBST, 
		    	  new Term[]{ t2(), t1()},
		    	  new ImmutableArray<QuantifiableVariable>(x),
		    	  null);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    public void testSubtermsForLogicVariable() {
	Exception exc=new Exception();
	try {
	    tf.createTerm(x,new Term[]{t3()});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException );
    }    
    

    public void testQuantifierWithNoBoundSubTerms() {
	Exception exc=new Exception();
        Term result = null;
	try {
	    result=TermBuilder.DF.all(ImmutableSLList.<QuantifiableVariable>nil(), t1());
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	Assert.assertEquals(result, t1());
    }
    

    public void testJunctorTermWithWrongArity() {
	Exception exc=new Exception();
	try {
	    tf.createTerm(Junctor.NOT, new Term[] {t1(), t2()});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }


    public void testSubSorts1() {
	tf.createTerm(g, new Term[]{tf.createTerm(v4), tf.createTerm(v1)});
	tf.createTerm(g, new Term[]{tf.createTerm(v4), tf.createTerm(v4)});
	tf.createTerm(g, new Term[]{tf.createTerm(v2), tf.createTerm(v3)});
	Exception exc=new Exception();
	try {
	    tf.createTerm(g, new Term[]{tf.createTerm(v1), tf.createTerm(v1)});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc=new Exception();
	try {
	    tf.createTerm(g, new Term[]{tf.createTerm(y), tf.createTerm(y)});
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    public void testSubSortsEquals() {
	tf.createTerm(Equality.EQUALS, tf.createTerm(v4), tf.createTerm(v1));
	tf.createTerm(Equality.EQUALS, tf.createTerm(v4), tf.createTerm(v4));
	tf.createTerm(Equality.EQUALS, tf.createTerm(v2), tf.createTerm(v3));
	tf.createTerm(Equality.EQUALS, tf.createTerm(x), tf.createTerm(z));
//	Exception exc = null;
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
	Term t = tf.createTerm(g, new Term[]{tf.createTerm(v2), 
				             tf.createTerm(v1)});
	Function c=new Function(new Name("c"), osort2, new Sort[0]);
	Term st = TermBuilder.DF.subst(WarySubstOp.SUBST, v2, 
					    tf.createTerm(c), t);
	c=new Function(new Name("c"), osort4, new Sort[0]);
	st = TermBuilder.DF.subst(WarySubstOp.SUBST, v2, 
					    tf.createTerm(c), t);
	c=new Function(new Name("c"), osort3, new Sort[0]);
	st = TermBuilder.DF.subst(WarySubstOp.SUBST, v1, 
					    tf.createTerm(c), t);
	Exception exc=new Exception();
	try {
	    c=new Function(new Name("c"), osort1, new Sort[0]);
	    st = TermBuilder.DF.subst(WarySubstOp.SUBST, v2, 
					    tf.createTerm(c), t);
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
	exc=new Exception();
	try {
	    c=new Function(new Name("c"), osort3, new Sort[0]);
	    st = TermBuilder.DF.subst(WarySubstOp.SUBST, v2, 
					   tf.createTerm(c), t);
	    
	} catch (TermCreationException e) {
	    exc=e;	    
	}
	assertTrue(exc instanceof TermCreationException);
    }

    /**
     * Tests the caching of {@link Term}s with and without {@link JavaBlock}s.
     */
    public void testCaching() {
       // Create Terms first time
       Term noJB = tf.createTerm(Junctor.TRUE);
       Term noJBWithChild = tf.createTerm(Junctor.NOT, noJB);
       JavaBlock javaBlock = JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
       Term withJB = tf.createTerm(Modality.DIA, new ImmutableArray<Term>(noJB), null, javaBlock);
       Term withJBChild = tf.createTerm(Junctor.NOT, withJB);
       Term withJBChildChild = tf.createTerm(Junctor.NOT, withJBChild);
       // Create Same terms again
       Term noJBAgain = tf.createTerm(Junctor.TRUE);
       Term noJBWithChildAgain = tf.createTerm(Junctor.NOT, noJB);
       JavaBlock javaBlockAgain = JavaBlock.createJavaBlock(new StatementBlock(new LocalVariableDeclaration()));
       Term withJBAgain = tf.createTerm(Modality.DIA, new ImmutableArray<Term>(noJB), null, javaBlockAgain);
       Term withJBChildAgain = tf.createTerm(Junctor.NOT, withJB);
       Term withJBChildChildAgain = tf.createTerm(Junctor.NOT, withJBChild);
       // Test caching
       assertSame(noJB, noJBAgain);
       assertSame(noJBWithChild, noJBWithChildAgain);
       assertNotSame(withJB, withJBAgain);
       assertNotSame(withJBChild, withJBChildAgain);
       assertNotSame(withJBChildChild, withJBChildChildAgain);
    }
}
