/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * An ArrayInitializer is a valid expression exclusively for initializing ArrayTypes. Any other
 * expressions are suited for any expression node. These rules could have been expressed by
 * appropriate types, but these solutions would require a couple of new interfaces which did not
 * seem adequate. The parent expression is either another ArrayInitializer (nested blocks) or a
 * VariableDeclaration.
 */

public class ArrayInitializer extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 7171507009155916797L;

    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;

    /**
     * Children.
     */

    protected ASTList<Expression> children;

    /**
     * Array initializer.
     */

    public ArrayInitializer() {
        super();
    }

    /**
     * Array initializer.
     *
     * @param args an expression mutable list.
     */

    public ArrayInitializer(ASTList<Expression> args) {
        setArguments(args);
        makeParentRoleValid();
    }

    /**
     * Array initializer.
     *
     * @param proto an array initializer.
     */

    protected ArrayInitializer(ArrayInitializer proto) {
        super(proto);
        if (proto.children != null) {
            children = proto.children.deepClone();
        }
        makeParentRoleValid();
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
     * Deep clone.
     *
     * @return the object.
     */

    public ArrayInitializer deepClone() {
        return new ArrayInitializer(this);
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
        // role 0 (IDX): subexpression
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

    public void accept(SourceVisitor v) {
        v.visitArrayInitializer(this);
    }
}
