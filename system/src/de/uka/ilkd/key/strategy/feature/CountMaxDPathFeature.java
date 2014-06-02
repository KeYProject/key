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
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Feature that returns the maximum number of literals occurring within a d-path
 * of the find-formula as a formula of the antecedent. Used terminology is
 * defined in Diss. by Martin Giese.
 */
public class CountMaxDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new CountMaxDPathFeature ();

    private CountMaxDPathFeature () {}
    
    @Override
    protected RuleAppCost doComputation (PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return NumberRuleAppCost.create ( maxDPath ( findTerm, !pos.isInAntec (), caches ) );
    }

}