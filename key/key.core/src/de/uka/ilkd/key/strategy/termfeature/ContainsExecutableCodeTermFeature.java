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

package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.Modality;


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
    
    protected boolean filter(Term t, Services services) {
        return containsExec ( t, services );
    }

    private boolean containsExec(Term t, Services services) {
        if ( t.isRigid () ) return false;
        //if ( t.isContainsJavaBlockRecursive() ) return true;
        
        final Operator op = t.op ();
        if ( op instanceof Quantifier ) return false;

        if ( op instanceof Modality ) return true;
        if ( considerQueries && op instanceof IProgramMethod ) return true;
        
        for ( int i = 0; i != op.arity (); ++i ) {
            final boolean res = filter ( t.sub ( i ), services );
            if ( res ) return true;
        }

        return false;
    }

}