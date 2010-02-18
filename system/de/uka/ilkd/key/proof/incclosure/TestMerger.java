// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import java.util.Iterator;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;



public class TestMerger extends TestCase {


    // Taken from TestConstraint.java

    private final static TermFactory tf=TermFactory.DEFAULT;
    private Services services;
    private Sort sort1;
    private Function f;
    private Constraint constraint_b;
    private Constraint constraint_a;
    private Function con;
    private Metavariable x;
    private Metavariable z;
    private Metavariable y;

   
    
    private Term term_f(TermSymbol var){
	Term t_x=tf.createFunctionTerm(var, new Term[]{});
	return term_f ( t_x );
    }
  
    private Term term_f(Term t){
	Term t_fx=tf.createFunctionTerm(f, t);
	return t_fx;
    }
  

    public TestMerger ( String name ) {
	super ( name );
    }

    public void setUp() {
        sort1 = new PrimitiveSort(new Name("S1"));
        f = new RigidFunction(new Name("f"),sort1, new Sort[]{sort1}); 
            // f(:S1):S1
        con = new RigidFunction(new Name("c"),sort1,new PrimitiveSort[0]);
        x = new Metavariable(new Name("x"),sort1);  //x:S1
        z = new Metavariable(new Name("z"),sort1); //z:S1
        y = new Metavariable(new Name("y"),sort1); //y:S1
        

        constraint_a = Constraint.BOTTOM
            .unify ( term_f ( x ), term_f ( con ), null )
            .unify ( term_f ( y ), term_f ( x ),  null );
       
        constraint_b = Constraint.BOTTOM
            .unify ( term_f ( x ), term_f ( con ), null )
            .unify ( term_f ( z ), term_f ( term_f ( con ) ), null );
        
        
        if (constraint_a == Constraint.TOP || 
                constraint_b == Constraint.TOP)
            throw new RuntimeException("Error setting up tests for Merger.");

        services = new Services();
    
        services.getNamespaces().sorts().add(sort1);       
    }
    
    public void tearDown() {
        services = null;
        sort1 = null;
        f = null;
        constraint_a = null;
        constraint_b = null;
        con = null;
        x = y = z = null;
    }
   

    public void doBufferSinkTests ( BufferSink s ) {
	assertTrue ( !s.isSatisfiable () && s.getConstraint () == Constraint.TOP );

	s.put ( constraint_a );
	assertTrue ( s.isSatisfiable () && s.getConstraint ().equals ( constraint_a ) );

	s.put ( constraint_a );
	assertTrue ( s.isSatisfiable () && s.getConstraint ().equals ( constraint_a ) );

	s.reset ( constraint_a );
	assertTrue ( s.isSatisfiable () && s.getConstraint ().equals ( constraint_a ) );

	s.put ( Constraint.TOP );
	assertTrue ( s.isSatisfiable () && s.getConstraint ().equals ( constraint_a ) );

	s.put ( Constraint.BOTTOM );
	assertTrue ( s.isSatisfiable () && s.getConstraint () == Constraint.BOTTOM );

	s.reset ( Constraint.TOP );
	assertTrue ( !s.isSatisfiable () && s.getConstraint () == Constraint.TOP );
	
	s.put ( constraint_a );
	s.put ( constraint_b );
	assertTrue ( s.isSatisfiable () &&
		     s.getConstraint ().isAsWeakAs ( constraint_a ) &&
		     s.getConstraint ().isAsWeakAs ( constraint_b ) );

	s.put ( Constraint.BOTTOM );
	assertTrue ( s.isSatisfiable () && s.getConstraint () == Constraint.BOTTOM );
    }

    
    public void testBufferSink () {
	{
	    BufferSink s = new BufferSink ( null );
	    doBufferSinkTests ( s );
	}

	{
	    BufferSink r = new BufferSink ( null );
	    BufferSink s = new BufferSink ( r );
	    doBufferSinkTests ( s );
	}
    }

    public void testMultiMerger () {
	BufferSink  root   = new BufferSink ( null );
	MultiMerger merger = new MultiMerger ( root, 3, services );

	BufferSink[] sinks = new BufferSink [5];
	Iterator<Sink> it = merger.getSinks ();
	sinks[0] = new BufferSink ( it.next () );
	sinks[1] = new BufferSink ( it.next () );
	sinks[2] = new BufferSink ( it.next () );

	doBufferSinkTests ( sinks[0] );
	sinks[0].reset ( Constraint.TOP );

	doBufferSinkTests ( sinks[1] );
	sinks[1].reset ( Constraint.TOP );

	sinks[0].put ( constraint_b );
	sinks[1].put ( constraint_b );
	sinks[2].put ( constraint_a );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a.join ( constraint_b, services ) ) );

	sinks[0].put ( constraint_a );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a.join ( constraint_b, services ) ) );

	sinks[1].put ( constraint_a );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a ) );

	sinks[2].put ( constraint_b );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals
		     ( IntersectionConstraint.intersect ( constraint_a,
							  constraint_b ) ) );

	sinks[2].put ( Constraint.BOTTOM );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals
		     ( IntersectionConstraint.intersect ( constraint_a,
							  constraint_b ) ) );

	sinks[0].reset ( Constraint.TOP );
	assertTrue ( !root.getConstraint ().isSatisfiable () &&
		     root.getConstraint () == Constraint.TOP );
	

	merger.expand ( 5 );
	it = merger.getSinks ();
	it.next (); it.next (); it.next ();
	sinks[3] = new BufferSink ( it.next () );
	sinks[4] = new BufferSink ( it.next () );

	sinks[0].put ( constraint_b );
	sinks[1].put ( constraint_b );
	sinks[2].put ( constraint_a );
	sinks[3].put ( constraint_b );
	sinks[4].put ( constraint_a );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a.join ( constraint_b, services ) ) );
	
	sinks[3].put ( Constraint.BOTTOM );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a.join ( constraint_b, services ) ) );

	sinks[4].put ( Constraint.TOP );
	assertTrue ( root.getConstraint ().isSatisfiable () &&
		     root.getConstraint ().equals ( constraint_a.join ( constraint_b, services ) ) );

	sinks[4].reset ( Constraint.TOP );
	assertTrue ( !root.getConstraint ().isSatisfiable () &&
		     root.getConstraint () == Constraint.TOP );
	
    
	assertTrue("No intersection sorts should have been introduced", 
            services.getNamespaces().sorts().allElements().size() == 1);
    }

}
