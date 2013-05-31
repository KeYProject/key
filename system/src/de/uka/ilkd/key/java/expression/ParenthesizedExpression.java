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



package de.uka.ilkd.key.java.expression;
import java.io.IOException;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/** Redundant Parentheses. Modelled as a special "identity" unary "infix"
 *  operator. */

public class ParenthesizedExpression extends Operator 					     
    implements ExpressionStatement, ReferencePrefix {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * In this case the order of the children is IMPORTANT. 
     * 	May contain:
     * 		several of Expression (should be one, the first is taken 
     *                         as parenthesized expression), 
     * 		Comments
     */
    public ParenthesizedExpression(ExtList children) {
	super(children);
    }

    public ParenthesizedExpression(Expression child) {
	super(child);
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
     *      Get arity.
     *      @return the int value.
     */
    public int getArity() {
        return 1;
    }

    /**
     *      Get precedence.
     *      @return the int value.
     */
    public int getPrecedence() {
        return 0;
    }

    /**
     *      Get notation.
     *      @return the int value.
     */
    public int getNotation() {
        return INFIX;
	/* Only unary infix operator;) */
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnParenthesizedExpression(this);
    }

    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printParenthesizedExpression(this);
    }

    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
	return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }


}
