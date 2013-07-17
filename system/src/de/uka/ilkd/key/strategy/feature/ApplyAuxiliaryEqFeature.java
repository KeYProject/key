// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.collection.ImmutableList;
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
 * This feature checks that an auxiliary equation is not applied to itself.
 * This means that the constrainted formula of the focus of the rule application
 * must not be part of the  if-formulas. If the rule application is
 * admissible, zero is returned.
 */
public class ApplyAuxiliaryEqFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new ApplyAuxiliaryEqFeature();

    private ApplyAuxiliaryEqFeature () {}
    
    protected boolean filter ( TacletApp p_app, PosInOccurrence pos, Goal goal ) {
        Debug.assertTrue ( pos != null, 
                "Need to know the position of " +
               "the application of the taclet" );

        if(!p_app.ifInstsComplete()) {
            return true;
        }

        ImmutableList<IfFormulaInstantiation> ifInsts = p_app.ifFormulaInstantiations();

        Debug.assertTrue ( ifInsts != null && !ifInsts.isEmpty(),
                   "Need to know the equation the taclet" +
                   " is used with" );

        for (IfFormulaInstantiation ifInst : ifInsts) {
            if (ifInst.getConstrainedFormula() == pos.constrainedFormula()) {
                return false;
            }
        }
        return true;
    }

}
