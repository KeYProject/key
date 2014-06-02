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
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;


/**
 * Term has the post condition term label.
 */
public final class IsPostConditionTermFeature extends BinaryTermFeature {

    public static final IsPostConditionTermFeature INSTANCE =
            new IsPostConditionTermFeature();


    private IsPostConditionTermFeature() {
    }


    @Override
    protected boolean filter(Term t, Services services) {
        return t.hasLabels() &&
               t.containsLabel(ParameterlessTermLabel.POST_CONDITION_LABEL);
    }
}
