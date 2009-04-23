// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class SeqContainsExecutableCodeFeature extends BinaryFeature {

    private final TermFeature tf;
    
    private SeqContainsExecutableCodeFeature(boolean considerQueries) {
        if ( considerQueries )
            tf = ContainsExecutableCodeTermFeature.PROGRAMS_OR_QUERIES;
        else
            tf = ContainsExecutableCodeTermFeature.PROGRAMS;
    }

    public final static Feature PROGRAMS =
        new SeqContainsExecutableCodeFeature ( false );
    public final static Feature PROGRAMS_OR_QUERIES =
        new SeqContainsExecutableCodeFeature ( true );

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        return containsExec ( goal.sequent ().succedent ().iterator () )
            || containsExec ( goal.sequent ().antecedent().iterator () );
    }

    private boolean containsExec(IteratorOfConstrainedFormula it) {
        while ( it.hasNext () ) {
            if ( tf.compute ( it.next ().formula () ).equals (
                 BinaryTermFeature.ZERO_COST ) )
                return true;
        }
        return false;
    }
}
