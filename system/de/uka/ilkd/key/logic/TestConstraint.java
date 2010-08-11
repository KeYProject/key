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

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;


/** class tests the constraint classes
*/


public class TestConstraint extends TestCase {
 
    TermFactory tf=TermFactory.DEFAULT;

    private Sort sort1=new PrimitiveSort(new Name("S1"));
    private Sort sort2=new PrimitiveSort(new Name("S2"));

    private Services DEFAULT = null;

    Function p=new RigidFunction(new Name("p"),Sort.FORMULA,new Sort[]{sort1});  
        //p(:S1):BOOL
   
    Function q=new RigidFunction(new Name("q"),Sort.FORMULA,new Sort[]{sort1, sort1, sort1});
      
    Function r=new RigidFunction(new Name("r"),Sort.FORMULA,new Sort[]{sort1, sort2});
        //r(:S1, :S2):BOOL
    Function r0=new RigidFunction(new Name("r0"),sort1,new Sort[]{sort1, sort1});
        //r(:S1, :S1):S1
    Function f=new RigidFunction(new Name("f"),sort1, new Sort[]{sort1}); 
        // f(:S1):S1
    Function h=new RigidFunction(new Name("h"),sort1, new Sort[]{sort1}); 
    // h(:S1):S1
    Function g=new RigidFunction(new Name("g"),sort1, new Sort[]{sort1, sort1}); 
        // g(:S1,S1):S1
    Function con=new RigidFunction(new Name("c"),sort1,new PrimitiveSort[0]);
    Metavariable x=new Metavariable(new Name("x"),sort1);  //x:S1
    Metavariable z=new Metavariable(new Name("z"),sort1); //z:S1
    Metavariable v=new Metavariable(new Name("v"),sort1); //v:S1
    Metavariable y=new Metavariable(new Name("y"),sort1); //y:S1
    Metavariable w=new Metavariable(new Name("w"),sort2); //w:S2
    Metavariable w0=new Metavariable(new Name("w0"),sort1); //w:S1

    LogicVariable lv0 = new LogicVariable ( new Name ( "lv0" ), sort1 ); //lv0:S1
    LogicVariable lv1 = new LogicVariable ( new Name ( "lv1" ), sort1 ); //lv1:S1

    public TestConstraint(String name) {
	super(name);
    }


    private Term term_p(TermSymbol var){
	Term t_x=tf.createFunctionTerm(var, new Term[]{});
	Term t_px=tf.createFunctionTerm(p, new Term[]{t_x});
	return t_px;
    }
  
    private Term term_r(TermSymbol o1S1,TermSymbol o2S2){
	Term t_x=tf.createFunctionTerm(o1S1, new Term[]{});
	Term t_w=tf.createFunctionTerm(o2S2, new Term[]{});
	return tf.createFunctionTerm(r, new Term[]{t_x,t_w});
    }

    public void setUp() { 
	
    }


    public void testSatisfiableConstraint1() {
	Constraint c=Constraint.BOTTOM.unify(term_p(x),term_p(con), DEFAULT);
	assertTrue(c.isSatisfiable() && 
		   ((EqualityConstraint)c).valueOf(x).equals(tf.createFunctionTerm(con,new Term[]{})));
    }
    
    public void testSatisfiableConstraint2() {
	Constraint c=Constraint.BOTTOM.unify(term_r(x,w),term_r(con,w), DEFAULT);
	assertTrue(c.isSatisfiable() && 
		   c!=Constraint.TOP &&
		   ((EqualityConstraint)c).valueOf(x).equals(tf.createFunctionTerm(con,new Term[]{})) &&
		   ((EqualityConstraint)c).isDefined(w)==false);
    }


    // unify(q(X,f(Y),Z),q(Z,X,Y))
    public void testCycle() {
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_fy=tf.createFunctionTerm(f, new Term[]{t1_y});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_x=tf.createFunctionTerm(x, new Term[]{});
	Term t2_y=tf.createFunctionTerm(y, new Term[]{});
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c=Constraint.BOTTOM.unify
	    (tf.createFunctionTerm(q,new Term[]{t1_x,t1_fy,t1_z}),
	     tf.createFunctionTerm(q,new Term[]{t2_z,t2_x,t2_y}), DEFAULT);
	assertTrue(c.isSatisfiable()==false);
	assertSame(c, Constraint.TOP);
    }

    // unify(q(X,Y,Z),q(Z,X,Y))
    public void testMVCycle() {
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_x=tf.createFunctionTerm(x, new Term[]{});
	Term t2_y=tf.createFunctionTerm(y, new Term[]{});
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c=Constraint.BOTTOM.unify
	    (tf.createFunctionTerm(q,new Term[]{t1_x,t1_y,t1_z}),
	     tf.createFunctionTerm(q,new Term[]{t2_z,t2_x,t2_y}), DEFAULT);
	assertTrue(c.isSatisfiable()==true);	
    }

    // join constraint {X=r0(Y,Z),Y=con} {Z=f(V),V=con}
    public void testJoinWithoutSubSume() {
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_v=tf.createFunctionTerm(v, new Term[]{});
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c1=Constraint.BOTTOM.unify
	    (t1_x,
	     tf.createFunctionTerm(r0,new Term[]{t1_y,t1_z}), DEFAULT);
	c1=c1.unify(t1_y,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);
	Constraint c2=Constraint.BOTTOM.unify
	    (t2_z,
	     tf.createFunctionTerm(f,new Term[]{t2_v}), DEFAULT);
	c2=c2.unify(t2_v,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);

	Constraint c3=Constraint.BOTTOM.unify
	    (t1_x,
	     tf.createFunctionTerm(r0,new Term[]{t1_y,t1_z}), DEFAULT);
	c3=c3.unify(t1_y,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);
	c3=c3.unify(t2_z,
	     tf.createFunctionTerm(f,new Term[]{t2_v}), DEFAULT);
	c3=c3.unify(t2_v,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);

	Constraint c4=c1.join(c2, DEFAULT);
	assertSame(c4,c4.join(c3, DEFAULT));
    }

    // join constraint {X=r0(Y,Z),Y=con} {X=r0(con,Z)}
    public void testJoinWithSubSume() {
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_x=tf.createFunctionTerm(x, new Term[]{});	
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c1=Constraint.BOTTOM.unify
	    (t1_x,
	     tf.createFunctionTerm(r0,new Term[]{t1_y,t1_z}), DEFAULT);
	c1=c1.unify(t1_y,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);
	Constraint c2=Constraint.BOTTOM.unify
	    (t2_x,
	     tf.createFunctionTerm(r0,new Term[]
		 {tf.createFunctionTerm(con,new Term[]{}), t2_z}), DEFAULT);

	BooleanContainer booleanCon=new BooleanContainer();
	assertEquals(c1.join(c2, DEFAULT, booleanCon),c1);
	assertTrue("Container says false instead of true",booleanCon.val());
    }


    public void testElmarsConstraint(){
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_fy=tf.createFunctionTerm(f, new Term[]{t1_y});
	Term t1_w=tf.createFunctionTerm(w0, new Term[]{});
	Term t1_gyw=tf.createFunctionTerm(g, new Term[]{t1_y,t1_w});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	
	Term t1_v=tf.createFunctionTerm(v, new Term[]{});

	Term t1_hv=tf.createFunctionTerm(h, new Term[]{t1_v});
	Term t1_gzhv=tf.createFunctionTerm(g, new Term[]{t1_z,t1_hv});	
	Term t1_fv=tf.createFunctionTerm(f, new Term[]{t1_v});
	Term t1_fx=tf.createFunctionTerm(f, new Term[]{t1_x});
	Term t1_ffx=tf.createFunctionTerm(f, new Term[]{t1_fx});
	
	Term t1_fz=tf.createFunctionTerm(f, new Term[]{t1_z});
	Term t1_ffz=tf.createFunctionTerm(f, new Term[]{t1_fz});
	Term t1_hffz=tf.createFunctionTerm(h, new Term[]{t1_ffz});
	Constraint c=Constraint.BOTTOM.unify(t1_x,t1_fy, DEFAULT);
	Constraint res=Constraint.BOTTOM.unify(t1_x,t1_fy, DEFAULT);
	c=c.unify(t1_gyw,t1_gzhv, DEFAULT).unify(t1_fv,t1_ffx, DEFAULT).unify(t1_w,t1_hffz, DEFAULT);
	res=res.unify(t1_x,t1_fy, DEFAULT).unify(t1_y,t1_z, DEFAULT).unify(t1_v,t1_fx, DEFAULT).unify(t1_w,t1_hv, DEFAULT);  
	assertSame(c.join(res, DEFAULT),c); // precond. if c subsumes res c==res
    }

    // intersect {X=r0(Y,Z),Y=con} {X=r0(con,Z)}
    public void testIntersectionConstraint0 () {	
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_x=tf.createFunctionTerm(x, new Term[]{});
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c1=Constraint.BOTTOM.unify
	    (t1_x,
	     tf.createFunctionTerm(r0,new Term[]{t1_y,t1_z}), DEFAULT);
	c1=c1.unify(t1_y,tf.createFunctionTerm(con,new Term[]{}), DEFAULT);
	Constraint c2=Constraint.BOTTOM.unify
	    (t2_x,
	     tf.createFunctionTerm(r0,new Term[]
		 {tf.createFunctionTerm(con,new Term[]{}), t2_z}), DEFAULT);

	ConstraintContainer cc = new ConstraintContainer ();

	assertSame ( IntersectionConstraint.intersect ( c1, c2, cc ), c2 );
	assertSame ( cc.val (), c2 );
	assertSame ( IntersectionConstraint.intersect ( c2, c1, cc ), c2 );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( Constraint.TOP, c1, cc ), c1 );
	assertSame ( cc.val (), c1 );
	assertSame ( IntersectionConstraint.intersect ( c2, Constraint.TOP, cc ), c2 );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( Constraint.BOTTOM, c2, cc ), Constraint.BOTTOM );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c1, Constraint.BOTTOM, cc ), Constraint.BOTTOM );
	assertSame ( cc.val (), Constraint.BOTTOM );
    }

    
    // intersect {X=r0(Y,Z)} {X=r0(con,Z)}
    public void testIntersectionConstraint1 () {
	Term t1_x=tf.createFunctionTerm(x, new Term[]{});
	Term t1_y=tf.createFunctionTerm(y, new Term[]{});
	Term t1_z=tf.createFunctionTerm(z, new Term[]{});
	Term t2_x=tf.createFunctionTerm(x, new Term[]{});
	Term t2_z=tf.createFunctionTerm(z, new Term[]{});
	Constraint c1=Constraint.BOTTOM.unify
	    (t1_x,
	     tf.createFunctionTerm(r0,new Term[]{t1_y,t1_z}), DEFAULT);
	Constraint c2=Constraint.BOTTOM.unify
	    (t2_x,
	     tf.createFunctionTerm(r0,new Term[]
		 {tf.createFunctionTerm(con,new Term[]{}), t2_z}), DEFAULT);

	ConstraintContainer cc  = new ConstraintContainer ();
	ConstraintContainer cc2 = new ConstraintContainer ();

	Constraint c3 = IntersectionConstraint.intersect ( c1, c2, cc );
	assertSame ( cc.val (), c2 );
	IntersectionConstraint.intersect ( c2, c3, cc );
	assertSame ( cc.val (), c1 );
	IntersectionConstraint.intersect ( c1, c3, cc );
	assertSame ( cc.val (), c2 );
	assertSame ( IntersectionConstraint.intersect ( c3, c1, cc ), c3 );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3, c2, cc ), c3 );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3, c3, cc ), c3 );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3,
							IntersectionConstraint.intersect ( Constraint.TOP, c3, cc ),
							cc2 ), c3 );
	assertSame ( cc2.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3, cc.val (), cc2 ), c3 );
	assertSame ( cc2.val (), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3, Constraint.TOP, cc ), c3 );
	assertSame ( cc.val (), Constraint.TOP );

	assertSame ( c3.join ( Constraint.TOP, DEFAULT ), Constraint.TOP );
	assertSame ( IntersectionConstraint.intersect ( c3, c3.join ( Constraint.BOTTOM, DEFAULT ) ), c3 );
	IntersectionConstraint.intersect ( c3.join ( Constraint.BOTTOM, DEFAULT ), c3, cc );
	assertSame ( cc.val (), Constraint.TOP );
	assertSame ( Constraint.TOP.join ( c3, DEFAULT ), Constraint.TOP );

	c3 = c3.join ( c3, DEFAULT );
	assertSame ( IntersectionConstraint.intersect ( c3, c1 ), c3 );
	assertSame ( IntersectionConstraint.intersect ( c3, c1 ), c3 );
    }


    // "all lv0. all lv1. p(lv1)"   and   "all lv1. all lv0. p(lv1)"
    // should not unify if the term "p(lv1)" is shared
    public void testBoundVariablesBug () {
	Term p_lv1 = tf.createFunctionTerm
	    (p, new Term[] { tf.createVariableTerm ( lv1 ) });

	Term _term0 = tf.createQuantifierTerm ( Op.ALL, lv1, p_lv1 );
	Term term0 = tf.createQuantifierTerm ( Op.ALL, lv0, _term0 );

	Term _term1 = tf.createQuantifierTerm ( Op.ALL, lv0, p_lv1 );
	Term term1 = tf.createQuantifierTerm ( Op.ALL, lv1, _term1 );

	assertSame ( "Terms " + term0 + " and " + term1 +
		     " should not be unifiable\n",
		     Constraint.BOTTOM.unify ( term0, term1, DEFAULT ),
		     Constraint.TOP );
    }

    
    public static void main(String[] args) {
	new TestConstraint("").testSatisfiableConstraint2();
    }

}
