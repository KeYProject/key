/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import org.antlr.v4.runtime.ParserRuleContext;
import recoder.java.*;
import recoder.java.statement.JavaStatement;

public class MergePointStatement extends JavaStatement implements ExpressionContainer {
    private static final long serialVersionUID = 8513553210611636414L;

    private StatementContainer astParent;
    private final ParserRuleContext mergeProc;

    // The indexPV is not used when parsing JML specs, but only for taclets
    protected Expression indexPV;

    public MergePointStatement(ParserRuleContext mergeProc) {
        makeParentRoleValid();
        this.mergeProc = mergeProc;
        this.indexPV = null;
    }

    public MergePointStatement() {
        this((ParserRuleContext) null);
    }

    /**
     * @param expr The index variable of the MergePointStatement
     */
    public MergePointStatement(Expression expr) {
        this.indexPV = expr;
        this.mergeProc = null;
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return astParent;
    }

    @Override
    public StatementContainer getStatementContainer() {
        return astParent;
    }

    @Override
    public void setStatementContainer(StatementContainer parent) {
        astParent = parent;
    }

    public ParserRuleContext getMergeProc() {
        return mergeProc;
    }

    public void setIndexPV(Expression indexPV) {
        this.indexPV = indexPV;
    }

    /**
     * Finds the source element that occurs first in the source.
     *
     * @return the last source element in the syntactical representation of this element, may be
     *         equals to this element.
     */
    @Override
    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     * Finds the source element that occurs last in the source.
     *
     * @return the last source element in the syntactical representation of this element, may be
     *         equals to this element.
     */
    @Override
    public SourceElement getLastElement() {
        return getChildCount() == 0 ? this : indexPV;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        return indexPV == null ? 0 : 1;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (indexPV != null && index == 0) {
            return indexPV;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (indexPV == p) {
            Expression r = (Expression) q;
            indexPV = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Ensures that each child has "this" as syntactical parent.
     */
    @Override
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        if (indexPV != null && indexPV == child) {
            return 0;
        }
        return -1;
    }

    public String getName() {
        return "//@ merge_point;";
    }

    @Override
    public void accept(SourceVisitor visitor) {
        // TODO: Check if we have to do anything
    }

    @Override
    public Statement deepClone() {
        throw new RuntimeException("Unimplemented");
    }

    @Override
    public Expression getExpressionAt(int index) {
        if (indexPV != null && index == 0) {
            return indexPV;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getExpressionCount() {
        return (indexPV != null) ? 1 : 0;
    }
}
