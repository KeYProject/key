// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SetAsListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.Feature;

public class SplittableQuantifiedFormulaFeature extends BinaryFeature {

    private SplittableQuantifiedFormulaFeature () {}
    
    public static final Feature INSTANCE =
        new SplittableQuantifiedFormulaFeature ();
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Analyser analyser = new Analyser ();
        if ( !analyser.analyse ( pos.constrainedFormula ().formula () ) )
            return false;

        if ( analyser.binOp == Op.AND )
            return TriggerUtils.intersect (
                   TriggerUtils.intersect (
                          analyser.left.freeVars (),
                          analyser.right.freeVars () ),
                          analyser.existentialVars )     .size () == 0;
        else if ( analyser.binOp == Op.OR )
            return TriggerUtils.intersect ( analyser.left.freeVars (),
                                               analyser.right.freeVars () )
                   .union ( analyser.existentialVars ).size ()
                   == analyser.existentialVars.size ();
        
        return false;
    }
    
    private static class Analyser {
        public SetOfQuantifiableVariable existentialVars =
            SetAsListOfQuantifiableVariable.EMPTY_SET;
        public Operator binOp;
        public Term left, right;
        
        public boolean analyse(Term formula) {
            final Operator op = formula.op();
            
            if ( op == Op.ALL ) {
                // might be that a variable is bound more than once
                existentialVars =
                    existentialVars.remove ( formula.varsBoundHere ( 0 )
                                             .lastQuantifiableVariable () );
                return analyse ( formula.sub ( 0 ) );
            }
            
            if ( op == Op.EX ) {
                existentialVars =
                    existentialVars.add ( formula.varsBoundHere ( 0 )
                                          .lastQuantifiableVariable () );
                return analyse ( formula.sub ( 0 ) );
            }

            if ( op == Op.AND || op == Op.OR ) {
                binOp = op;
                left = formula.sub ( 0 );
                right = formula.sub ( 1 );
                return true;
            }

            return false;
        }
    }    
}
