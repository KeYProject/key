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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Switch.
 */

public class Switch extends BranchStatement
    implements ExpressionContainer,
    VariableScope, TypeScope {

    /**
 *      Branches.
     */

    protected final ImmutableArray<Branch> branches;

    /**
 *      Expression.
     */

    protected final Expression expression;



    /**
 *      Switch.
     */

    public Switch() {
	this.branches=null;
        this.expression=null;
    }

    /**
 *      Switch.
 *      @param e an expression.
     */

    public Switch(Expression e) {
	this.branches=null;
        this.expression=e;
    }

    /**
 *      Switch.
 *      @param e an expression.
 *      @param branches a branch array
     */

    public Switch(Expression e, Branch[] branches) {
	this.branches=new ImmutableArray<Branch>(branches);
        this.expression=e;
    }

    /**
 *      Switch.
 *      @param children a list with all children
     */

    public Switch(ExtList children) {
        super(children);
	this.expression = children.get(Expression.class);
	this.branches=new ImmutableArray<Branch>(children.collect(Branch.class)); 
    }


    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (expression != null) result++;
        if (branches   != null) result += branches.size();
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
        if (branches != null) {
            return branches.get(index);
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
 *      Get the number of branches in this container.
 *      @return the number of branches.
     */

    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
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
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /* Return the branch array wrapper
     * @return the array wrapper of the branches
     */
    public ImmutableArray<Branch> getBranchList() {
	return branches;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnSwitch(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSwitch(this);
    }
}
