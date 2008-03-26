// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns true iff the hyper-tableaux simplification method
 * approves the given application (which is supposed to be the application of a
 * replace-known rule). Used terminology is defined in Diss. by Martin Giese.
 */
public class SimplifyReplaceKnownCandidateFeature
       extends AbstractPolarityFeature implements Feature {

    public final static Feature INSTANCE =
        new SimplifyReplaceKnownCandidateFeature ();
    
    private SimplifyReplaceKnownCandidateFeature () {}
    
    /**
     * Compute the cost of a RuleApp.
     * @param ruleApp the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of <code>app</code>
     */
    public RuleAppCost compute (RuleApp ruleApp, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        
        if ( !isAllowedPosition ( pos ) ) return BinaryFeature.TOP_COST;
        
        assert ruleApp instanceof TacletApp : "Feature is only applicable to taclet apps";

        final TacletApp app = (TacletApp)ruleApp;
        final Sequent ifSeq = app.taclet ().ifSequent ();
        
        assert ifSeq.size () == 1 : "Wrong number of if-formulas.";
                
        final Boolean pol = polarity ( pos, new Boolean ( pos.isInAntec () ) );

        final boolean ifForInAntec =
            ifSeq.succedent () == Semisequent.EMPTY_SEMISEQUENT;        
        
        final boolean approved =
                 pol == null
                 || pol.booleanValue () != ifForInAntec
                 || AbstractBetaFeature.alwaysReplace ( pos.subTerm () );
        
        return approved ? BinaryFeature.ZERO_COST : BinaryFeature.TOP_COST;
    }

    private boolean isAllowedPosition ( PosInOccurrence pos ) {
        final PIOPathIterator it = pos.iterator ();
        
        while ( it.next() != -1 ) {
            if ( !( it.getSubTerm().op() instanceof IUpdateOperator ) )
                return true;
        }
        
        return false;
    }
}
