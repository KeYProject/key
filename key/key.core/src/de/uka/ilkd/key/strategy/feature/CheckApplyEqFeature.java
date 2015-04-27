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

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

/**
 * This feature checks that an equation is not applied to itself. This means
 * that the focus of the rule application must not be one side of an equation
 * that is the instantiation of the first if-formula. If the rule application is
 * admissible, zero is returned.
 */
public class CheckApplyEqFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new CheckApplyEqFeature();

    private CheckApplyEqFeature () {}
    
    protected boolean filter ( TacletApp p_app, PosInOccurrence pos, Goal goal ) {
        Debug.assertTrue ( pos != null, 
                "Need to know the position of " +
               "the application of the taclet" );
    
        IfFormulaInstantiation ifInst = p_app.ifFormulaInstantiations ().head ();

        Debug.assertTrue ( ifInst != null,
                   "Need to know the equation the taclet" +
                   " is used with" );

        return isNotSelfApplication ( pos, ifInst )
//               && equationIsDirected ( ifInst, p_app.constraint() )
               ;
    }

    private boolean isNotSelfApplication(PosInOccurrence pos,
                                         IfFormulaInstantiation ifInst) {
        if ( ! ( ifInst instanceof IfFormulaInstSeq )
             || ifInst.getConstrainedFormula () != pos.constrainedFormula ()
             || ( (IfFormulaInstSeq)ifInst ).inAntec () != pos.isInAntec () )
                return true;
        
        // Position may not be one of the terms compared in
        // the equation

        final PIOPathIterator it = pos.iterator ();

        it.next ();

        // leading updates are not interesting
        while ( it.getSubTerm ().op () instanceof UpdateApplication ) {
            if ( !it.hasNext () ) return true;
            it.next ();
        }

        if ( ! ( it.getSubTerm ().op () instanceof Equality ) || !it.hasNext () )
                return true;

        if ( it.getChild () == 0 )
        // we don't allow rewriting in the left term of the equation
                return false;

        return true;
    }

}