/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator base class.
 *
 * @author AL
 */

public abstract class Operator extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {
    protected final ImmutableArray<Expression> children;

    /**
     * Relative positioning of the operator.
     */
    public static final int PREFIX = 0;
    public static final int INFIX = 1;
    public static final int POSTFIX = 2;

    protected Operator() {
        this.children = null;
    }

    /**
     * Operator.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */
    protected Operator(Expression lhs, Expression rhs) {
        this.children = new ImmutableArray<>(lhs, rhs);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. In this case the order of
     *        the children is IMPORTANT. May contain: 2 of Expression (the first Expression as left
     *        hand side, the second as right hand side), Comments
     *
     */
    protected Operator(ExtList children) {
        super(children);
        this.children = new ImmutableArray<>(children.collect(Expression.class));
    }

    /**
     * Operator.
     *
     * @param unaryChild an expression.
     */

    protected Operator(Expression unaryChild) {
        this.children = new ImmutableArray<>(unaryChild);
    }

    /**
     * Operator.
     *
     * @param arguments an array of expression.
     */

    protected Operator(Expression[] arguments) {
        this.children = new ImmutableArray<>(arguments);
    }


    /**
     * getArity() == getASTchildren().size()
     */
    public abstract int getArity();

    /**
     * 0 is the "highest" precedence (obtained by parantheses), 13 the "lowest".
     */

    public abstract int getPrecedence();

    /**
     * @return true, if a has a higher priority (a lower precendence value) than b.
     */

    public static boolean precedes(Operator a, Operator b) {
        return a.getPrecedence() < b.getPrecedence();
    }

    /**
     * @return INFIX, PREFIX, or POSTFIX.
     */
    public abstract int getNotation();

    /**
     * Checks if this operator is left or right associative. The associativity defines the order in
     * which the arguments are evaluated (left-to-right or right-to-left). The default is left
     * associative. Unary operators, assignments and conditionals are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>false</CODE> otherwise.
     */
    public boolean isLeftAssociative() {
        return true;
    }

    public SourceElement getFirstElement() {
        return switch (getNotation()) {
            case INFIX, POSTFIX -> children.get(0).getFirstElement();
            default -> this;
        };
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return switch (getNotation()) {
            case INFIX, POSTFIX -> children.get(0).getFirstElementIncludingBlocks();
            default -> this;
        };
    }

    public SourceElement getLastElement() {
        return switch (getNotation()) {
            case INFIX, PREFIX -> children.get(getArity() - 1).getLastElement();
            default -> this;
        };
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (children != null) ? children.size() : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (children != null) ? children.size() : 0;
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
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** return arguments */
    public ImmutableArray<Expression> getArguments() {
        return children;
    }

    // has to be changed
    public boolean isToBeParenthesized() {
        return false;
    }

    /**
     * overriden from JavaProgramElement.
     */
    public String reuseSignature(Services services, ExecutionContext ec) {
        return super.reuseSignature(services, ec) + "("
            + services.getTypeConverter().getKeYJavaType(this, ec).getName() + ")";
    }

    public abstract KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);

}
