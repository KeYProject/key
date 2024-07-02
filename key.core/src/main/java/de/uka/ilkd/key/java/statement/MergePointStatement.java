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

package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * A statement indicating a merge point.
 *
 * @author Dominic Scheurer
 */
public class MergePointStatement extends JavaStatement
        implements ExpressionContainer {

    // Those are used for JML to JavaDL conversions
    protected final IProgramVariable identifier;
    protected final Comment[] comments;

    public MergePointStatement(IProgramVariable indexPV) {
        this.identifier = indexPV;
        this.comments = null;
    }

    public MergePointStatement(LocationVariable identifier, Comment[] comments) {
        this.identifier = identifier;
        this.comments = comments;
    }

    public MergePointStatement(ExtList children) {
        super(children);
        identifier = children.get(IProgramVariable.class);
        assert identifier instanceof IProgramVariable;
        comments = children.get(Comment[].class);
    }

    @Override
    public Comment[] getComments() {
        return comments;
    }

    /**
     * Get the number of expressions in this container.
     * 
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (identifier != null) ? 1 : 0;
    }

    /**
     * Return the expression at the specified index in this node's "virtual"
     * expression array.
     * 
     * @param index
     *            an index for an expression.
     * 
     * @return the expression with the given index.
     * 
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (identifier != null && index == 0) {
            return (Expression) identifier;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     * 
     * @return the expression.
     */
    public Expression getExpression() {
        return (Expression) identifier;
    }

    /**
     * Returns the number of children of this node.
     * 
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (identifier != null)
            result++;
        return result;
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
    public ProgramElement getChildAt(int index) {
        if (identifier != null) {
            if (index == 0)
                return identifier;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     * 
     * @param v
     *            the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnMergePointStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMergePointStatementBlock(this);
    }
}