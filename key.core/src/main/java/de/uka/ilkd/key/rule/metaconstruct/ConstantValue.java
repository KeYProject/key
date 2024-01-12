/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replace a program variable that is a compile-time constant with the value of the initializer
 */
public final class ConstantValue extends AbstractTermTransformer {


    public ConstantValue() {
        super(new Name("#constantvalue"), 1);
    }


    public Term transform(Term term, SVInstantiations svInst, Services services) {
        term = term.sub(0);
        Operator op = term.op();

        if (op instanceof ProgramConstant) {
            Literal lit = ((ProgramConstant) op).getCompileTimeConstant();
            if (lit != null) {
                term = services.getTypeConverter().convertToLogicElement(lit);
            }
        }

        return term;
    }
}
