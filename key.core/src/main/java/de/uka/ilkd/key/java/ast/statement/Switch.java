/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;

import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.LinkedList;

/**
 * Switch.
 */

public class Switch extends BranchStatement
        implements ExpressionContainer, VariableScope, TypeScope, ProgramPrefix {

    /**
     * Branches.
     */

    protected final ImmutableArray<SwitchBranch> branches;

    /**
     * Expression.
     */

    protected final Expression expression;

    private final int prefixLength;

    private final MethodFrame innerMostMethodFrame;

    /**
     * Switch.
     */

    public Switch() {
        this.branches = null;
        this.expression = null;
        prefixLength = 0;
        innerMostMethodFrame = null;
    }

    /**
     * Switch.
     *
     * @param e
     *        an expression.
     */

    public Switch(Expression e) {
        this.branches = null;
        this.expression = e;
        prefixLength = 0;
        innerMostMethodFrame = null;
    }

    /**
     * Switch.
     *
     * @param e
     *        an expression.
     * @param branches
     *        a branch array
     */

    public Switch(Expression e, SwitchBranch[] branches) {
        this.branches = new ImmutableArray<>(branches);
        this.expression = e;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    /**
     * Switch.
     *
     * @param children
     *        a list with all children
     */

    public Switch(ExtList children) {
        super(children);
        this.expression = children.get(Expression.class);
        this.branches = new ImmutableArray<>(children.collect(SwitchBranch.class));
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    public Switch(PositionInfo pi, List<Comment> c, Expression expr,
            ImmutableArray<Branch> branches) {
        super(pi, c);
        this.expression = expr;
        this.branches = branches;
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (expression != null) {
            result++;
        }
        if (branches != null) {
            result += branches.size();
        }
        return result;
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
        if (expression != null) {
            if (index == 0) {
                return expression;
            }
            index--;
        }
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
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
        if (expression != null && index == 0) {
            return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     *
     * @return the expression.
     */

    public Expression getExpression() {
        return expression;
    }


    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
    }

    /*
     * Return the branch at the specified index in this node's "virtual" branch array.
     *
     * @param index an index for a branch.
     *
     * @return the branch with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public SwitchBranch getBranchAt(int index) {
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /*
     * Return the branch array wrapper
     *
     * @return the array wrapper of the branches
     */
    public ImmutableArray<SwitchBranch> getBranchList() {
        return branches;
    }

    @Override
    public SourceElement getFirstElement() {
        if (branches.isEmpty()) return this;
        return branches.get(0);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnSwitch(this);
    }

    @Override
    public boolean hasNextPrefixElement() {
        return !branches.isEmpty() && branches.get(0) instanceof ProgramPrefix;
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) branches.get(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }

    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? ((ProgramPrefix) branches.get(0)).getLastPrefixElement()
                : this;
    }

    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    @Override
    public MethodFrame getInnerMostMethodFrame() {
        return innerMostMethodFrame;
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return StatementBlock.computePrefixElements(this);
    }

    /**
     * The method checks whether the expression in the synchronized prefix is either a local
     * variable or a meta class reference (as local variables of this type are not supported by KeY,
     * see return value for {@link MetaClassReference#getKeYJavaType(Services, ExecutionContext)}.
     *
     * @return true iff the above stated condition holds.
     */
    private boolean expressionWithoutSideffects() {
        return (expression instanceof ProgramVariable && !((ProgramVariable) expression).isMember())
                || (expression instanceof MetaClassReference);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return branches.isEmpty() ? PosInProgram.TOP : (expressionWithoutSideffects()
                ? PosInProgram.ONE
                : PosInProgram.TOP);
    }
}
