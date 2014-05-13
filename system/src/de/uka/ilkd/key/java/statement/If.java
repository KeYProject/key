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

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  If.
 *  @author <TT>AutoDoc</TT>
 */
public class If extends BranchStatement implements ExpressionContainer {

    /**
     *      Then branch.
     */

    protected Then thenBranch;

    /**
     *      Else branch.
     */

    protected Else elseBranch;

    /**
     *      Expression.
     */

    protected Expression expression;

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: Comments, a Then, an Else, an Expression (as condition of If)
     */ 
    public If(ExtList children) {
	super(children);
	thenBranch=children.get(Then.class);
	elseBranch=children.get(Else.class);
	expression=children.get(Expression.class);
    }

    /**
     *      If.
     *      @param e an expression.
     *      @param thenBranch a then.
     */

    public If(Expression e, Then thenBranch) {
        this(e, thenBranch, null);
    }

    /**
     *      If.
     *      @param e an expression.
     *      @param thenBranch a then.
     *      @param elseBranch an else.
     */

    public If(Expression e, Then thenBranch, Else elseBranch) {
        if (e == null) {
            throw new NullPointerException();
        }
        expression = e;
        this.thenBranch=thenBranch;
        this.elseBranch=elseBranch;
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (expression != null) result++;
        if (thenBranch != null) result++;
        if (elseBranch != null) result++;
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
        if (expression != null) {
            if (index == 0) return expression;
            index--;
        }
        if (thenBranch != null) {
            if (index == 0) return thenBranch;
            index--;
        }
        if (elseBranch != null) {
            if (index == 0) return elseBranch;
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
     *      Get expression.
     *      @return the expression.
     */

    public Expression getExpression() {
        return expression;
    }
   
    /**
     *      Get then.
     *      @return the then.
     */
    public Then getThen() {
        return thenBranch;
    }

    /**
     *      Get else.
     *      @return the else.
     */
    public Else getElse() {
        return elseBranch;
    }

    /**
     *      Get the number of branches in this container.
     *      @return the number of branches.
     */
    public int getBranchCount() {
        int result = 0;
        if (thenBranch != null) result += 1;
        if (elseBranch != null) result += 1;
        return result;
    }

    /*
      Return the branch at the specified index in this node's
      "virtual" branch array.
      @param index an index for a branch.
      @return the branch with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Branch getBranchAt(int index) {
        if (thenBranch != null) {
            if (index == 0) {
                return thenBranch;
            }
            index -= 1;
        }
        if (elseBranch != null) {
            if (index == 0) {
                return elseBranch;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Add (or replace) an else-branch
     *      @author vladimir
     */
    public void addBranch(Else el) {
       this.elseBranch = el;

    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnIf(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printIf(this);
    }
}