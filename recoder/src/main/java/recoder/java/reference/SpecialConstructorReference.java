/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * Occurs in a constructor declaration as the first statement as this(...) or super(...) reference.
 * The Reference knows the constructor declaration it refers to.
 */

public abstract class SpecialConstructorReference extends JavaNonTerminalProgramElement
        implements ConstructorReference {

    /**
     * Parent.
     */

    protected StatementContainer parent;

    /**
     * Arguments.
     */

    protected ASTList<Expression> arguments;

    /**
     * Special constructor reference.
     */

    public SpecialConstructorReference() {
        // nothing to do
    }

    /**
     * Special constructor reference.
     *
     * @param arguments an expression mutable list.
     */

    public SpecialConstructorReference(ASTList<Expression> arguments) {
        setArguments(arguments);
    }

    /**
     * Special constructor reference.
     *
     * @param proto a special constructor reference.
     */

    protected SpecialConstructorReference(SpecialConstructorReference proto) {
        super(proto);
        if (proto.arguments != null) {
            arguments = proto.arguments.deepClone();
        }
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (arguments != null) {
            for (int i = arguments.size() - 1; i >= 0; i -= 1) {
                arguments.get(i).setExpressionContainer(this);
            }
        }
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */

    public StatementContainer getStatementContainer() {
        return parent;
    }

    /**
     * Set statement container.
     *
     * @param s a statement container.
     */

    public void setStatementContainer(StatementContainer s) {
        parent = s;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (arguments != null) ? arguments.size() : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
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
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (arguments != null) {
            return arguments.get(index);
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
        count = (arguments == null) ? 0 : arguments.size();
        for (int i = 0; i < count; i++) {
            if (arguments.get(i) == p) {
                if (q == null) {
                    arguments.remove(i);
                } else {
                    Expression r = (Expression) q;
                    arguments.set(i, r);
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
        return arguments;
    }

    /**
     * Set arguments.
     *
     * @param list an expression mutable list.
     */

    public void setArguments(ASTList<Expression> list) {
        arguments = list;
    }
}
