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

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * Binary feature that returns zero iff a certain Taclet app has not already
 * been performed. Contrary to <code>NonDuplicateAppFeature</code>, this feature
 * is also able to handle failing meta-constructs correctly (these constructs
 * return equal, but not identical formulas in case of a failure), but is less
 * efficient.
 */
public class EqNonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new EqNonDuplicateAppFeature ();

    private EqNonDuplicateAppFeature () {}
    
    public boolean filter (TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        if ( !app.ifInstsComplete () ) return true;

        return noDuplicateFindTaclet ( app, pos, goal );
    }

    protected boolean semiSequentContains(Semisequent semisequent,
                                          SequentFormula cfma) {
        return semisequent.containsEqual ( cfma );
    }

    protected boolean comparePio(TacletApp newApp,
                                 TacletApp oldApp,
                                 PosInOccurrence newPio, PosInOccurrence oldPio) {
        return oldPio.eqEquals ( newPio );
    }
}
