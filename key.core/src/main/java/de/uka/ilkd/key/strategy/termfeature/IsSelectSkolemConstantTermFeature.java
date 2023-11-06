/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;


/**
 * A schema variable that is used as placeholder for auxiliary heap skolem constants.
 */
public final class IsSelectSkolemConstantTermFeature extends BinaryTermFeature {

    public static final IsSelectSkolemConstantTermFeature INSTANCE =
        new IsSelectSkolemConstantTermFeature();


    private IsSelectSkolemConstantTermFeature() {
    }


    @Override
    protected boolean filter(Term t, Services services) {
        return t.hasLabels() && t.containsLabel(ParameterlessTermLabel.SELECT_SKOLEM_LABEL)
                && t.op().arity() == 0 && t.op() instanceof Function;
    }
}
