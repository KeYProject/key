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
