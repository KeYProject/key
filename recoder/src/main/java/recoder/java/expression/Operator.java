/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Operator base class.
 *
 * @author AL
 */

public abstract class Operator extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {

    /**
     * Relative positioning of the operator.
     */

    public final static int PREFIX = 0, INFIX = 1, POSTFIX = 2;
    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;
    /**
     * Children.
     */

    protected ASTList<Expression> children;

    /**
     * Operator.
     */

    public Operator() {
        // nothing to do
    }

    /**
     * Operator.
     *
     * @param unaryChild an expression.
     */

    public Operator(Expression unaryChild) {
        children = new ASTArrayList<>(getArity());
        children.add(unaryChild);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Operator.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Operator(Expression lhs, Expression rhs) {
        children = new ASTArrayList<>(getArity());
        children.add(lhs);
        children.add(rhs);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Operator.
     *
     * @param proto an operator.
     */

    protected Operator(Operator proto) {
        super(proto);
        if (proto.children != null) {
            children = proto.children.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * @return true, if a has a higher priority (a lower precendence value) than b.
     */

    public static boolean precedes(Operator a, Operator b) {
        return a.getPrecedence() < b.getPrecedence();
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (children != null) {
            for (int i = children.size() - 1; i >= 0; i -= 1) {
                children.get(i).setExpressionContainer(this);
            }
        }
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
     * @return INFIX, PREFIX, or POSTFIX.
     */

    public abstract int getNotation();

    /**
     * Checks if this operator is left or right associative. The associativity defines the order in
     * which the arguments are evaluated (left-to-right or right-to-left). The default is left
     * associative. Unary operators, assignments and conditionals are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>
     * false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return true;
    }

    public SourceElement getFirstElement() {
        switch (getNotation()) {
        case INFIX:
        case POSTFIX:
            return children.get(0).getFirstElement();
        case PREFIX:
        default:
            return this;
        }
    }

    public SourceElement getLastElement() {
        switch (getNotation()) {
        case INFIX:
        case PREFIX:
            return children.get(getArity() - 1).getLastElement();
        case POSTFIX:
        default:
            return this;
        }
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return expressionParent;
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
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): subexpression, or parameters
        // role 1: type reference (for type operators only)
        // role 2: prefix (for New only)
        // role 3: class declaration (for New and EnumConstructorInvocation only), or
        // array initializer (for NewArray)
        if (children != null) {
            int index = children.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        return -1;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
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
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        int count;
        count = (children == null) ? 0 : children.size();
        for (int i = 0; i < count; i++) {
            if (children.get(i) == p) {
                if (q == null) {
                    children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get arguments.
     *
     * @return the expression mutable list.
     */

    public ASTList<Expression> getArguments() {
        return children;
    }

    /**
     * Set arguments.
     *
     * @param list an expression mutable list.
     */

    public void setArguments(ASTList<Expression> list) {
        children = list;
    }

    /**
     * Is to be parenthesized.
     *
     * @return the boolean value.
     */

    public boolean isToBeParenthesized() {
        return (expressionParent instanceof Operator)
                && (!(expressionParent instanceof ReferencePrefix))
                && (((Operator) expressionParent).getPrecedence() < getPrecedence
                /*
                 * ReferencePrefices include ParenthesizedExpressions, New, NewArray; these all come
                 * with parentheses.
                 */());
    }

}
