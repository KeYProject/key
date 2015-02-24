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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

/**
 * This feature checks that the position of application is not contained in the
 * if-formulas. If the rule application is admissible, zero is returned.
 */
public class NoSelfApplicationFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new NoSelfApplicationFeature();

    private NoSelfApplicationFeature() {}

    @Override
    protected boolean filter ( TacletApp p_app, PosInOccurrence pos, Goal goal ) {
        Debug.assertTrue ( pos != null,
                "NoSelfApplicationFeature: Need to know the position of the application of the taclet" );

        if(!p_app.ifInstsComplete()) {
            return true;
        }

        ImmutableList<IfFormulaInstantiation> ifInsts = p_app.ifFormulaInstantiations();

        Debug.assertTrue ( ifInsts != null && !ifInsts.isEmpty(),
                   "NoSelfApplicationFeature: Need to know the equation the taclet is used with" );

        boolean noSelfApplication = true;
        for (IfFormulaInstantiation ifInst : ifInsts) {
            noSelfApplication = noSelfApplication &&
                                (ifInst.getConstrainedFormula() != pos.constrainedFormula());
        }
        return noSelfApplication;
    }

}