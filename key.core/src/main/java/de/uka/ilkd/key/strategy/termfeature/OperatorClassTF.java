/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Term feature for checking whether the top operator of a term has an instance of a certain class
 */
public class OperatorClassTF extends BinaryTermFeature {

    private final Class<? extends Operator> opClass;

    private OperatorClassTF(Class<? extends Operator> op) {
        this.opClass = op;
    }

    public static TermFeature create(Class<? extends Operator> op) {
        return new OperatorClassTF(op);
    }

    protected boolean filter(Term term, Services services) {
        return opClass.isInstance(term.op());
    }
}
