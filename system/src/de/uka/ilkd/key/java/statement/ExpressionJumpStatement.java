// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Expression jump statement.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class ExpressionJumpStatement extends JumpStatement implements ExpressionContainer {

    /**
     *      Expression.
     */

    protected final Expression expression;

    /**
     * Expression jump statement.
     * May contain: 	an Expression (as expression of the
     * 			ExpressionJumpStatement), 
     * 		Comments
     */
    public ExpressionJumpStatement(ExtList children) {
	super(children);
	expression=children.get(Expression.class);	
    }

    /**
     *      Expression jump statement.
     */
    public ExpressionJumpStatement() {
	expression=null;
    }

    /**
     *      Expression jump statement.
     * @param expr an Expression used to jump 
     */
    public ExpressionJumpStatement(Expression expr) {
	expression=expr;
    }

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */
    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /**
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
     *      Get expression.
     *      @return the expression.
     */
    public Expression getExpression() {
        return expression;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return (expression != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     *  @param index an index into this node's "virtual" child array
     *  @return the program element at the given position
     *  @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *             of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (expression != null) {
            if (index == 0) return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
}
