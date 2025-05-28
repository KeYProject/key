/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.costbased.MutableState;

/// Term feature for checking whether the top operator of a term is identical to a given one
public class OperatorTF extends BinaryTermFeature {

    private final Operator op;

    private OperatorTF(Operator op) {
        this.op = op;
    }

    public static TermFeature create(Operator op) {
        return new OperatorTF(op);
    }

    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        return op == term.op();
    }
}
