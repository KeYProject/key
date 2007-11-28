// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;

/** class tests the PosInOccurrence
*/


public class TestPosInOcc extends TestCase {

    public TestPosInOcc(String name) {
	super(name);
    }

    public void testIterator () {
	TermFactory tf=TermFactory.DEFAULT;
	Sort sort1=new PrimitiveSort(new Name("S1"));
	Metavariable x=new Metavariable(new Name("x"),sort1);  
	Function f=new RigidFunction(new Name("f"),sort1,new Sort[]{sort1});
	Function p=new RigidFunction(new Name("p"),Sort.FORMULA,new Sort[]{sort1});

	Term terms[] = new Term [ 3 ];
	terms[0]     = tf.createFunctionTerm ( x );
	terms[1]     = tf.createFunctionTerm ( f, new Term[] { terms[0] } );
	terms[2]     = tf.createFunctionTerm ( p, new Term[] { terms[1] } );

	PosInOccurrence pio = new PosInOccurrence
	    ( new ConstrainedFormula ( terms[2], Constraint.BOTTOM ),
	      PosInTerm.TOP_LEVEL,
	    true);

	PIOPathIterator it = pio.iterator ();

	// a top-level position

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == -1 );

	// two nodes deeper

	pio = pio.down ( 0 ).down ( 0 );
	it = pio.iterator ();

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[0] &&
		     it.getPosInOccurrence ().subTerm () == terms[0] &&
		     it.getChild () == -1 );

	assertFalse ( it.hasNext () );

	// add a term below a metavariable

	pio = pio.setTermBelowMetavariable ( terms[1] );
	it = pio.iterator ();

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == -1 );

	assertFalse ( it.hasNext () );

	// add a term below a metavariable

	pio = pio.down ( 0 );
	it = pio.iterator ();

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[0] &&
		     it.getPosInOccurrence ().subTerm () == terms[0] &&
		     it.getChild () == -1 );

	assertFalse ( it.hasNext () );

	// without the <code>hasNext()</code>-calls

	it = pio.iterator ();

	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == 0 );

	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[0] &&
		     it.getPosInOccurrence ().subTerm () == terms[0] &&
		     it.getChild () == -1 );
    }

    
    public void testReplaceConstrainedFormula () {
        TermFactory tf = TermFactory.DEFAULT;
        Sort sort1 = new PrimitiveSort ( new Name ( "S1" ) );
        Metavariable x = new Metavariable ( new Name ( "x" ), sort1 );
        Metavariable y = new Metavariable ( new Name ( "y" ), sort1 );
        Function c = new RigidFunction ( new Name ( "c" ), sort1, new Sort[] {} );
        Function f = new RigidFunction ( new Name ( "f" ),
                                    sort1,
                                    new Sort[] { sort1 } );
        Function p = new RigidFunction ( new Name ( "p" ),
                                    Sort.FORMULA,
                                    new Sort[] { sort1 } );

        Term terms[] = new Term[3];
        terms[0] = tf.createFunctionTerm ( x );
        terms[1] = tf.createFunctionTerm ( f, new Term[] { terms[0] } );
        terms[2] = tf.createFunctionTerm ( p, new Term[] { terms[1] } );
        ConstrainedFormula cfma = new ConstrainedFormula ( terms[2] );

        Term terms2[] = new Term[4];
        terms2[0] = tf.createFunctionTerm ( c );
        terms2[1] = tf.createFunctionTerm ( f, new Term[] { terms2[0] } );
        terms2[2] = tf.createFunctionTerm ( f, new Term[] { terms2[1] } );
        terms2[3] = tf.createFunctionTerm ( p, new Term[] { terms2[2] } );
        ConstrainedFormula cfma2 = new ConstrainedFormula ( terms2[3] );

        Term terms3[] = new Term[4];
        terms3[0] = tf.createFunctionTerm ( y );
        terms3[1] = tf.createFunctionTerm ( f, new Term[] { terms3[0] } );
        terms3[2] = tf.createFunctionTerm ( f, new Term[] { terms3[1] } );
        terms3[3] = tf.createFunctionTerm ( p, new Term[] { terms3[2] } );
        ConstrainedFormula cfma3 = new ConstrainedFormula ( terms3[3] );

        final PosInOccurrence topPIO = new PosInOccurrence ( cfma,
                                                             PosInTerm.TOP_LEVEL,
                                                             true );




        // Test without metavariables involved
        PosInOccurrence pio = topPIO.down ( 0 );
        assertTrue ( pio.subTerm () == terms[1] );
        PosInOccurrence pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[2] );

        // PIO pointing to metavariable, without term below
        pio = topPIO.down ( 0 ).down ( 0 );
        assertTrue ( pio.subTerm () == terms[0] );
        pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[1] );

        // PIO pointing to a term that is mounted below a metavariable
        pio = topPIO.down ( 0 ).down ( 0 ).setTermBelowMetavariable ( terms2[1] );
        assertTrue ( pio.subTerm () == terms2[1] );
        pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[1] );

        // PIO pointing to a position within a term that is mounted below a
        // metavariable
        pio = topPIO.down ( 0 ).down ( 0 )
            .setTermBelowMetavariable ( terms2[1] ).down ( 0 );
        assertTrue ( pio.subTerm () == terms2[0] );
        pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[0] );

        // PIO pointing to a position (a metavariable) within a term that is
	// mounted below a metavariable
        pio = topPIO.down ( 0 ).down ( 0 )
            .setTermBelowMetavariable ( terms3[1] ).down ( 0 );
        assertTrue ( pio.subTerm () == terms3[0] );
        pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma3 );
        assertTrue ( pio.subTerm () == terms3[0] );

        // PIO pointing to a position within a term that is mounted below a
        // metavariable
        pio = topPIO.down ( 0 ).down ( 0 )
            .setTermBelowMetavariable ( terms2[2] ).down ( 0 );
        assertTrue ( pio.subTerm () == terms2[1] );
        pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[0] );
    }
}
