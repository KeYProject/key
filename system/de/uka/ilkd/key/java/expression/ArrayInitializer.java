// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


/**
 *  An ArrayInitializer is a valid expression exclusively for initializing
 *  ArrayTypes. Any other expressions are suited for any expression node.
 *  These rules could have been expressed by appropriate types, but these
 *  solutions would require a couple of new interfaces which did not seem
 *  adequate.
 *  The parent expression is either another ArrayInitializer (nested blocks)
 *  or a VariableDeclaration.
 */

public class ArrayInitializer
 extends JavaNonTerminalProgramElement
 implements Expression, ExpressionContainer {

    /**
 *      Children.
     */

    protected final ArrayOfExpression children;


    /**
     *  Array initializer.
     *  @param list with all children.
     * 	 May contain: 
     * 		several of Expression (as the initializing expression)
     * 		Comments
     */

    public ArrayInitializer(ExtList list) {
	super(list);
	this.children = 
	    new ArrayOfExpression((Expression[])list.collect(Expression.class));
    }
    
    /**
     * create a new array initializer with the given expressions as elements.
     * @param list of all contained elements
     */
    public ArrayInitializer(Expression[] expressions) {
        super();
        this.children = new ArrayOfExpression(expressions);
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
            return children.getExpression(index);
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
            return children.getExpression(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnArrayInitializer(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printArrayInitializer(this);
    }

    /**
     *      Get arguments.
     *      @return the wrapped argument array
     */
    public ArrayOfExpression getArguments() {
        return children;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	Expression i = this;
	int n = 0;
	Sort s=null;
	for(;i instanceof ArrayInitializer && ((ArrayInitializer)i).getChildCount()!=0 ;
	    i=((ArrayInitializer)i).getExpressionAt(0)){
	    n++;
	}
	s = i.getKeYJavaType(javaServ, ec).getSort();        
        final JavaInfo javaInfo = javaServ.getJavaInfo(); 
	return javaInfo.getKeYJavaType
	    (ArraySortImpl.getArraySortForDim(s, n, 
					      javaInfo.getJavaLangObjectAsSort(), 
                                              javaInfo.getJavaLangCloneableAsSort(),
                                              javaInfo.getJavaIoSerializableAsSort()));
    }


}
