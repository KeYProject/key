/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator.adt;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class SetUnion extends BinaryOperator {
    public SetUnion(PositionInfo pi, List<Comment> c, Expression a, Expression b) {
        super(pi, c, a, b);
    }

    public SetUnion(ExtList changeList) {
        super(changeList);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return Operator.PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSetUnion(this);
    }

}
