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
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already
 * been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature ();

    protected boolean containsRuleApp (ImmutableList<RuleApp> list,
                                       TacletApp rapp,
                                       PosInOccurrence pio) {

        for (RuleApp aList : list) {
            if (sameApplication(aList, rapp, pio)) return true;
        }

        return false;
    }

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if ( !app.ifInstsComplete () ) {
            return true;
        }

        if ( pos == null ) {
            return !containsRuleApp ( goal.appliedRuleApps (), app, pos );
        }

        return noDuplicateFindTaclet ( app, pos, goal );
    }

    protected boolean comparePio(TacletApp newApp,
                                 TacletApp oldApp,
                                 PosInOccurrence newPio, PosInOccurrence oldPio) {
        return oldPio.equals ( newPio );
    }

    protected boolean semiSequentContains(Semisequent semisequent,
                                          SequentFormula cfma) {
        return semisequent.contains ( cfma );
    }
}