/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator.mset;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class MSetDiff extends BinaryOperator {
    public MSetDiff(ExtList children) {
        super(children);
    }

    public MSetDiff(Expression msetA, Expression msetB) {
        super(msetA, msetB);
    }



    @Override
    public void visit(Visitor v) {
        v.performActionOnMSetDiff(this);
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }
}
