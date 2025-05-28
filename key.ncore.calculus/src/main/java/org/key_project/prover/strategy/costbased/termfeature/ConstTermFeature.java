/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;

/// A feature that returns a constant value
public class ConstTermFeature implements TermFeature {
    public RuleAppCost compute(Term term, MutableState mState, LogicServices services) {
        return val;
    }

    private ConstTermFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static TermFeature createConst(RuleAppCost p_val) {
        return new ConstTermFeature(p_val);
    }

    private final RuleAppCost val;
}
