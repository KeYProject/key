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

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns zero iff the focus of a rule contains a
 * quantifier
 * 
 * NB: this can nowadays be done more nicely using term features
 */
public class ContainsQuantifierFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new ContainsQuantifierFeature ();

    private ContainsQuantifierFeature () {}
    
    @Override
    protected RuleAppCost doComputation (PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return containsQuantifier ( findTerm, caches )
                     ? BinaryFeature.ZERO_COST
                     : BinaryFeature.TOP_COST;
    }

}