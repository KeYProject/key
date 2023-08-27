/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * This class encapsulates updates of a for loop
 */
public class ForUpdates extends JavaNonTerminalProgramElement
        implements ExpressionContainer, IForUpdates {

    final ImmutableArray<Expression> updates;

    public ForUpdates(ImmutableArray<Expression> exprarr) {
        updates = exprarr;
    }

    public ForUpdates(ExtList ups, PositionInfo pos) {
        super(pos);
        Expression[] exps = new Expression[ups.size()];
        for (int i = 0; i < exps.length; i++) {
            exps[i] = (Expression) ups.get(i);
        }
        updates = new ImmutableArray<>(exps);
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
