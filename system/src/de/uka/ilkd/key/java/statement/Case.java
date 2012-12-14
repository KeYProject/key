// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Case.
 * 
 */
public class Case extends BranchImp implements ExpressionContainer {

    /**
     *      Expression.
     */
    protected final Expression expression;

    /**
     *      Body.
     */
    protected final ImmutableArray<Statement> body;

    /**
     *      Case.
     */
    public Case() {
	this.expression=null;
	this.body=null;
    }

    /**
     *      Case.
     *      @param e an expression.
     */
    public Case(Expression e) {
	this.expression=e;
	this.body=null;
    }

    /**
     *      Case.
     *      @param e an expression.
     *      @param body a statement mutable list.
     */
    public Case(Expression e, Statement[] body) {
	this.body=new ImmutableArray<Statement>(body);
        this.expression=e;
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: Comments
     *              a Statement (as the statement following case)
     * Must NOT contain: an Expression indicating the condition of the case
     * as there are classes that are Expression and Statement, so they might
     * get mixed up. Use the second parameter of this constructor for the
     * expression.
     * @param expr the expression of the case
     */ 
    public Case(ExtList children, Expression expr, PositionInfo pos) {
	super(children, pos);
	this.expression=expr;
	this.body=new ImmutableArray<Statement>(children.collect(Statement.class)); 
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (expression != null) result++;
        if (body       != null) result += body.size();
        return result;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
        int len;
        if (expression != null) {
            if (index == 0) return expression;
            index--;
        }
        if (body != null) {
            len = body.size();
            if (len > index) {
                return body.get(index);
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */

    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
        if (expression != null && index == 0) {
            return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */
    public int getStatementCount() {
        return (body != null) ? body.size() : 0;
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Statement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get expression.
     *      @return the expression.
     */
    public Expression getExpression() {
        return expression;
    }

    /**
     *      The body may be empty (null), to define a fall-through.
     *      Attaching an {@link EmptyStatement} would create a single ";".
     */
    public ImmutableArray<Statement> getBody() {
        return body;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnCase(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCase(this);
    }
}
