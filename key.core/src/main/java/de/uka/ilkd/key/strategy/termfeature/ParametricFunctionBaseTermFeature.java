/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

/**
 * Returns zero iff the term's operator is an instance of the given parametric function
 * (independent of their sorts).
 * Similar as
 * {@link org.key_project.prover.strategy.costbased.termfeature.OperatorTF}
 * but for a parametric function symbols.
 */
public class ParametricFunctionBaseTermFeature extends BinaryTermFeature {

    private final ParametricFunctionDecl base;

    private ParametricFunctionBaseTermFeature(ParametricFunctionDecl base) {
        this.base = base;
    }

    public static TermFeature create(ParametricFunctionDecl base) {
        return new ParametricFunctionBaseTermFeature(base);
    }

    @Override
    protected boolean filter(Term t, MutableState mState, LogicServices services) {
        return t.op() instanceof ParametricFunctionInstance instance
                && instance.getBase() == base;
    }
}
