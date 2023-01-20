/*
 * This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0
 */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;


/**
 * Term has the post condition term label.
 */
public final class IsPostConditionTermFeature extends BinaryTermFeature {

    public static final IsPostConditionTermFeature INSTANCE = new IsPostConditionTermFeature();


    private IsPostConditionTermFeature() {}


    @Override
    protected boolean filter(Term t, Services services) {
        return t.hasLabels() && t.containsLabel(ParameterlessTermLabel.POST_CONDITION_LABEL);
    }
}
