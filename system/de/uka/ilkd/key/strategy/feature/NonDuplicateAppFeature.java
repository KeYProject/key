// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IteratorOfRuleApp;
import de.uka.ilkd.key.rule.ListOfRuleApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already
 * been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature ();

    protected boolean containsRuleApp (ListOfRuleApp list,
                                       TacletApp rapp,
                                       PosInOccurrence pio) {

        final IteratorOfRuleApp it = list.iterator ();
        while ( it.hasNext () ) {
            if ( sameApplication ( it.next (), rapp, pio ) ) return true;
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
                                          ConstrainedFormula cfma) {
        return semisequent.contains ( cfma );
    }
}
