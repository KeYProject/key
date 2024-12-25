/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.ExpressionContainer;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

public class ForUpdates extends JavaNonTerminalProgramElement
        implements ExpressionContainer, IForUpdates {

    final ImmutableArray<Expression> updates;

    public ForUpdates(ImmutableArray<Expression> exprarr) {
        updates = exprarr;
    }


    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return updates.size();
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     *
     * @return the expression with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        return updates.get(index);
    }

    public int size() {
        return getExpressionCount();
    }

    public ImmutableArray<Expression> getUpdates() {
        return updates;
    }

    public void visit(Visitor v) {
        v.performActionOnForUpdates(this);
    }

    public int getChildCount() {
        return getExpressionCount();
    }

    public ProgramElement getChildAt(int index) {
        return getExpressionAt(index);
    }

}
