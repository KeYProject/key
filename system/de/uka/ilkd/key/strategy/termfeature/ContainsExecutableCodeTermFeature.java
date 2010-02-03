// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.Quantifier;

/**
 * Returns zero iff a term contains a program or (optionally) a query expression
 */
public class ContainsExecutableCodeTermFeature extends BinaryTermFeature {

    private final boolean considerQueries;

    private ContainsExecutableCodeTermFeature(boolean considerQueries) {
        this.considerQueries = considerQueries;
    }

    public final static TermFeature PROGRAMS =
        new ContainsExecutableCodeTermFeature ( false );
    public final static TermFeature PROGRAMS_OR_QUERIES =
        new ContainsExecutableCodeTermFeature ( true );
    
    protected boolean filter(Term t) {
        return containsExec ( t );
    }

    private boolean containsExec(Term t) {
        if ( t.isRigid () ) return false;

        final Operator op = t.op ();
        if ( op instanceof Quantifier ) return false;

        if ( op instanceof Modality ) return true;
        if ( considerQueries && op instanceof ProgramMethod ) return true;
        
        for ( int i = 0; i != op.arity (); ++i ) {
            final boolean res = filter ( t.sub ( i ) );
            if ( res ) return true;
        }

        return false;
    }

}
