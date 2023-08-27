/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Loop scope block. TODO
 *
 * @author Dominic Scheurer
 */
public class LoopScopeBlock extends JavaStatement
        implements StatementContainer, ExpressionContainer, ProgramPrefix {

    protected final IProgramVariable indexPV;
    protected final StatementBlock body;
    private final MethodFrame innerMostMethodFrame;
    private final int prefixLength;

    /**
     * TODO
     *
     * @param body
     */
    public LoopScopeBlock(StatementBlock body) {
        this.body = body;
        this.indexPV = null;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    /**
     * TODO
     *
     * @param e
     * @param body
     */
    public LoopScopeBlock(IProgramVariable iProgramVariable, StatementBlock body) {
        this.indexPV = iProgramVariable;
        this.body = body;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    /**
     * Synchronized block.
     *
     * @param children a list with all children
     */
    public LoopScopeBlock(ExtList children) {
        super(children);
        indexPV = children.get(IProgramVariable.class);
        body = children.get(StatementBlock.class);
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    @Override
    public boolean hasNextPrefixElement() {
        return !body.isEmpty() && body.getStatementAt(0) instanceof ProgramPrefix;
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) body.getStatementAt(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }

    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
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
        return StatementBlock.computePrefixElements(body.getBody(), this);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return getStatementCount() == 0 ? PosInProgram.TOP
                : PosInProgram.TOP.down(getChildCount() - 1).down(0);
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    @Override
    public int getExpressionCount() {
        return (indexPV != null) ? 1 : 0;
    }

    /**
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     * @return the expression with the given index.
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    @Override
    public Expression getExpressionAt(int index) {
        if (indexPV != null && index == 0) {
            return (ProgramVariable) indexPV; // XXX This cast may fail...
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     *
     * @return the expression.
     */
    public IProgramVariable getIndexPV() {
        return indexPV;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int result = 0;
        if (indexPV != null) {
            result++;
        }
        if (body != null) {
            result++;
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (indexPV != null) {
            if (index == 0) {
                return indexPV;
            }
            index--;
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get body.
     *
     * @return the statement block.
     */
    public StatementBlock getBody() {
        return body;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    @Override
    public int getStatementCount() {
        return (body != null && !body.isEmpty()) ? 1 : 0;
    }

    /**
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    @Override
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public SourceElement getFirstElement() {
        return body.getFirstElement();
    }

    /**
     * Calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopScopeBlock(this);
    }
}
