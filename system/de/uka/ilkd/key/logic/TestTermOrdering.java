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

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Tests for the term ordering classes
 */


public class TestTermOrdering extends TestCase {

    TermFactory tf=TermFactory.DEFAULT;

    private Sort sort1=new PrimitiveSort(new Name("S1"));

    Function f=new RigidFunction(new Name("f"),sort1, new Sort[]{sort1}); 
        // f(:S1):S1
    Function h=new RigidFunction(new Name("h"),sort1, new Sort[]{sort1}); 
    // h(:S1):S1
    Function g=new RigidFunction(new Name("g"),sort1, new Sort[]{sort1, sort1}); 
        // g(:S1,S1):S1
    Function c=new RigidFunction(new Name("c"),sort1, new Sort[]{}); 
        // c:S1
    Function z=new RigidFunction(new Name("z"),sort1, new Sort[]{}); 
        // z:S1

    ProgramVariable pv=new LocationVariable (new ProgramElementName ("pv"), sort1);

    Metavariable x=new Metavariable(new Name("x"),sort1);  //x:S1
    Metavariable y=new Metavariable(new Name("y"),sort1); //y:S1

    TermOrdering depthO     = new DepthTermOrdering ();
    TermOrdering nameO      = new NameTermOrdering ();
    TermOrdering depthnameO =
	new CascadeDepthTermOrdering ( new NameTermOrdering () );

    public TestTermOrdering(String name) {
	super(name);
    }

    // f(op)
    private Term term_f(Operator op){
	Term t_c=term_const(op);
	return term_f ( t_c );
    }
    
    private Term term_const(Operator op){
	return tf.createFunctionTerm(op);
    }

    // f(t)
    private Term term_f(Term t){
	Term t_ft=tf.createFunctionTerm(f, t);
	return t_ft;
    }
    
    // g(t, t2)
    private Term term_g(Term t, Term t2){
	Term t_g=tf.createFunctionTerm(g, new Term[] {t, t2});
	return t_g;
    }    


    public void testEqual () {
	// !( f(c) < f(c) )
	Term t = term_f ( c );
	assertTrue ( depthO.compare ( t, t ) == 0 );
	assertTrue ( nameO.compare ( t, t ) == 0 );
	assertTrue ( depthnameO.compare ( t, t ) == 0 );

	// !( f(x) < f(x) )
	t = term_f ( x );
	assertTrue ( depthO.compare ( t, t ) == 0 );
	assertTrue ( nameO.compare ( t, t ) == 0 );
	assertTrue ( depthnameO.compare ( t, t ) == 0 );
    }

    public void testNameOrdering () {
	// c < f(c)
	Term t  = term_const ( c );
	Term t2 = term_f ( c );
	assertTrue ( nameO.compare ( t, t2 ) < 0 );
	assertTrue ( nameO.compare ( t2, t ) > 0 );
	
	// f(c) < f(f(c))
	t  = term_f ( c );
	t2 = term_f ( term_f ( c ) );
	assertTrue ( nameO.compare ( t, t2 ) < 0 );
	assertTrue ( nameO.compare ( t2, t ) > 0 );
	
	// f(c) < f(f(x))
	t2 = term_f ( term_f ( x ) );
	assertTrue ( nameO.compare ( t, t2 ) < 0 );
	assertTrue ( nameO.compare ( t2, t ) > 0 );

	// f(z) <> f(f(x))
	t  = term_f ( z );
	assertTrue ( nameO.compare ( t, t2 ) == 0 );

	// f(z) > f(f(c))
	t2 = term_f ( term_f ( c ) );
	assertTrue ( nameO.compare ( t, t2 ) > 0 );
	assertTrue ( nameO.compare ( t2, t ) < 0 );

	// f(z) <> f(x)
	t2 = term_f ( x );
	assertTrue ( nameO.compare ( t, t2 ) == 0 );

	// f(pv) <> f(x)
	t  = term_f ( pv );
	assertTrue ( nameO.compare ( t, t2 ) == 0 );

	// f(pv) > f(c)
	t2 = term_f ( c );
	assertTrue ( nameO.compare ( t, t2 ) > 0 );
	assertTrue ( nameO.compare ( t2, t ) < 0 );

	// f(pv) > f(z)
	t2 = term_f ( z );
	assertTrue ( nameO.compare ( t, t2 ) > 0 );
	assertTrue ( nameO.compare ( t2, t ) < 0 );
    }

    public void testDepthOrdering () {
	// f(c) < f(f(c))
	Term t  = term_f ( c );
	Term t2 = term_f ( term_f ( c ) );
	assertTrue ( depthO.compare ( t, t2 ) < 0 );
	assertTrue ( depthO.compare ( t2, t ) > 0 );
	
	assertTrue ( depthnameO.compare ( t, t2 ) < 0 );
	assertTrue ( depthnameO.compare ( t2, t ) > 0 );
	
	// f(c) < f(f(x))
	t2 = term_f ( term_f ( x ) );
	assertTrue ( depthO.compare ( t, t2 ) < 0 );
	assertTrue ( depthO.compare ( t2, t ) > 0 );
	
	assertTrue ( depthnameO.compare ( t, t2 ) < 0 );
	assertTrue ( depthnameO.compare ( t2, t ) > 0 );

	// f(c) <> f(z)
	t2 = term_f ( z );
	assertTrue ( depthO.compare ( t, t2 ) == 0 );

	// g(x,y) <> f(g(x,x))
	t  = term_g ( term_const ( x ), term_const ( y ) );
	t2 = term_f ( term_g ( term_const ( x ), term_const ( x ) ) );
	assertTrue ( depthO.compare ( t, t2 ) == 0 );

	assertTrue ( depthnameO.compare ( t, t2 ) == 0 );
    }

    public void testDepthNameOrdering () {
	// f(z) < f(f(c))
	Term t  = term_f ( z );
	Term t2 = term_f ( term_f ( c ) );
	assertTrue ( depthnameO.compare ( t, t2 ) < 0 );
	assertTrue ( depthnameO.compare ( t2, t ) > 0 );
	
	// f(z) <> f(x)
	t2 = term_f ( x );
	assertTrue ( depthnameO.compare ( t, t2 ) == 0 );

	// f(c) < f(z)
	t  = term_f ( c );
	t2 = term_f ( z );
	assertTrue ( depthnameO.compare ( t, t2 ) < 0 );
	assertTrue ( depthnameO.compare ( t2, t ) > 0 );
    }

    // The examples from the script "Automatisches Beweisen"
    public void testDepthScript () {
	// g(x,f(c)) <> g(x,f(x))
	Term t  = term_g ( term_const ( x ), term_f ( c ) );
	Term t2 = term_g ( term_const ( x ), term_f ( x ) );
	assertTrue ( depthO.compare ( t, t2 ) == 0 );
	
	// g(x,y) < f(g(x,y))
	t  = term_g ( term_const ( x ), term_const ( y ) );
	t2 = term_f ( t );
	assertTrue ( depthO.compare ( t, t2 ) < 0 );
	assertTrue ( depthO.compare ( t2, t ) > 0 );

	// g(x,c) <> g(f(c),x)
	t  = term_g ( term_const ( x ), term_const ( c ) );
	t2 = term_g ( term_f ( c ), term_const ( x ) );
	assertTrue ( depthO.compare ( t, t2 ) == 0 );
    }

}
