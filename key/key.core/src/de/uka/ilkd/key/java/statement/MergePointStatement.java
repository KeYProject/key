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

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * A statement indicating a merge point.
 *
 * @author Dominic Scheurer
 */
public class MergePointStatement extends JavaStatement
        implements ExpressionContainer {

    protected final Expression expression;

    public MergePointStatement() {
        this.expression = null;
    }

    public MergePointStatement(Expression expression) {
        this.expression = expression;
    }

    public MergePointStatement(ExtList children) {
        super(children);
        expression = children.get(Expression.class);
        assert expression instanceof IProgramVariable;
    }

    @Override
    public int hashCode() {
        return 17 * super.hashCode() + expression.hashCode();
    }

    /**
     * Get the number of expressions in this container.
     * 
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
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
     * Returns the number of children of this node.
     * 
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (expression != null)
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
        if (expression != null) {
            if (index == 0)
                return expression;
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
        //TODO (DS): Probably have to do something with ProgramElementReplaceVisitor or the like
        v.performActionOnMergePointStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMergePointStatementBlock(this);
    }
}