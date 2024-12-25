/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.reference;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Occurs in a constructor declaration as the first statement as this(...) or super(...) reference.
 * The Reference knows the constructor declaration it refers to.
 */

public abstract class SpecialConstructorReference extends JavaNonTerminalProgramElement
        implements ConstructorReference {



    protected final ImmutableArray<Expression> arguments;



    public SpecialConstructorReference() {
        this.arguments = null;
    }

    /**
     * Special constructor reference.
     *
     * @param arguments
     *        an expression mutable list.
     */
    public SpecialConstructorReference(Expression[] arguments) {
        this.arguments = new ImmutableArray<>(arguments);
    }


    /**
     * Special constructor reference.
     *
     * @param arguments
     *        an expression mutable list.
     */
    public SpecialConstructorReference(ImmutableArray<Expression> arguments) {
        this.arguments = arguments;
    }

    public SpecialConstructorReference(ImmutableArray<Expression> arguments, PositionInfo pi,
            List<Comment> c) {
        super(pi, c);
        this.arguments = arguments;
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return getExpressionCount();
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (arguments != null) {
            return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (arguments != null) ? arguments.size() : 0;
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
        if (arguments != null) {
            return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get arguments.
     *
     * @return the expression mutable list.
     */
    public ImmutableArray<Expression> getArguments() {
        return arguments;
    }
}
