// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.speclang.PositionedString;
import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementContainer;
import recoder.java.statement.JavaStatement;

@SuppressWarnings("serial")
public class MergePointStatement extends JavaStatement
        implements ExpressionContainer {

    private StatementContainer astParent;
    private final PositionedString mergeProc;
    private final PositionedString mergeParams;

    // The indexPV is not used when parsing JML specs, but only for taclets
    protected Expression indexPV;

    public MergePointStatement(PositionedString mergeProc,
            PositionedString mergeParams) {
        makeParentRoleValid();
        this.mergeProc = mergeProc;
        this.mergeParams = mergeParams;
        this.indexPV = null;
    }

    public MergePointStatement() {
        this(null, null);
    }

    /**
     * @param expr
     *            The index variable of the MergePointStatement
     */
    public MergePointStatement(Expression expr) {
        this.indexPV = expr;

        this.mergeProc = null;
        this.mergeParams = null;
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

    public PositionedString getMergeProc() {
        return mergeProc;
    }

    public PositionedString getMergeParams() {
        return mergeParams;
    }
    
    public void setIndexPV(Expression indexPV) {
        this.indexPV = indexPV;
    }

    /**
     * Finds the source element that occurs first in the source.
     * 
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     */
    @Override
    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     * Finds the source element that occurs last in the source.
     * 
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
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
     * Returns the child at the specified index in this node's "virtual" child
     * array
     * 
     * @param index
     *            an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds
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