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

package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.util.ExtList;

/**
 *    Operator base class.
 *    @author AL
*/

public abstract class Operator extends JavaNonTerminalProgramElement
    implements Expression, ExpressionContainer {


    /**
     *      Children.
     */
    protected final ImmutableArray<Expression> children;


    /**
     *      Relative positioning of the operator.
     */

    public static final int PREFIX = 0;
    public static final int INFIX = 1;
    public static final int POSTFIX = 2;

    public Operator() {
	this.children = null;
    }

    /**
     Operator.
     @param lhs an expression.
     @param rhs an expression.
     */
    public Operator(Expression lhs, Expression rhs) {
	this.children=new ImmutableArray<Expression>(lhs, rhs);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * In this case the order of the children is IMPORTANT. 
     * 	May contain:
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments
     *
     */
    public Operator(ExtList children) {
        super(children);
	this.children =
	    new ImmutableArray<Expression>
	    (children.collect(Expression.class)); 
    }

    /**
     * Operator.
     * @param unaryChild an expression.
     */

    public Operator(Expression unaryChild) {
	this.children = new ImmutableArray<Expression>(unaryChild);
    }

    /**
     * Operator.
     * @param arguments an array of expression.
     */

    public Operator(Expression[] arguments) {
	this.children = new ImmutableArray<Expression>(arguments);
    }


    /** 
     * getArity() == getASTchildren().size() 
     */
    public abstract int getArity();

    /** 0 is the "highest" precedence (obtained by parantheses),
     *  13 the "lowest". 
     */

    public abstract int getPrecedence();

    /**
     *    @return true, if a has a higher priority (a lower precendence value)
     *      than b.
     */

    public static boolean precedes(Operator a, Operator b) {
        return a.getPrecedence() < b.getPrecedence();
    }

    /**
     *      @return INFIX, PREFIX, or POSTFIX.
     */
    public abstract int getNotation();

    /**
     *  Checks if this operator is left or right associative. The associativity
     *  defines the order in which the arguments are evaluated (left-to-right
     *  or right-to-left). The default is left associative. Unary operators,
     *  assignments and conditionals are right associative.
     *  @return <CODE>true</CODE>, if the operator is left associative,
     *   <CODE>false</CODE> otherwise.
     */
    public boolean isLeftAssociative() {
        return true;
    }

    public SourceElement getFirstElement() {
        switch (getNotation()) {
        case INFIX:
        case POSTFIX:
            return children.get(0).getFirstElement();
        case PREFIX:
        default:
            return this;
        }
    }

    public SourceElement getLastElement() {
        switch (getNotation()) {
        case INFIX:
        case PREFIX:
            return children.get(getArity() - 1).getLastElement();
            case POSTFIX:
        default:
            return this;
        }
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (children != null) ? children.size() : 0;
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
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */

    public int getExpressionCount() {
        return (children != null) ? children.size() : 0;
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
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** return arguments */
    public ImmutableArray<Expression> getArguments() {
	return children;
    }

    // has to be changed
    public boolean isToBeParenthesized() {
	return false;
    }
    
    /** overriden from JavaProgramElement. 
     */
    public String reuseSignature(Services services, ExecutionContext ec) {
       return super.reuseSignature(services, ec)+"("+
          services.getTypeConverter().getKeYJavaType(this, ec).getName()+")";
    }

    public abstract KeYJavaType getKeYJavaType(Services javaServ, 
					       ExecutionContext ec);

}