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

package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  The array allocation operator.
 *  There are two variants for NewArray:
 *  <OL>
 *  <LI>Ordinary array construction
 *  <BR><tt>new XYZ[d<sub>1</sub>]...[d<sub>n</sub>]</tt>
 *  <LI>Initialized array construction
 *  <BR><tt>new XYZ[]...[] { a<sub>1</sub>, ..., a<sub>n</sub> }
 *  </OL>
 *  Contrary to an ordinary New, a NewArray is no ConstructorReference (since
 *  all ArrayType constructors are predefined) and is not used as a Statement
 *  (since there are no sideeffects in the constructor). No access path is
 *  required for new, since there is no inner class problem.
 *  <P>
 *  NewArray has either a list of dimension length expressions, or
 *  a single ArrayInitializer.
 */

public class NewArray extends TypeOperator
 implements Reference, ReferencePrefix {

    /**
     *      Dimensions.
     */

    protected final int dimensions;

    
    /**
     *      Array initializer.
     */

    protected final ArrayInitializer arrayInitializer;

    /**
     * the key java type of this array
     */
    private final KeYJavaType keyJavaType;


    /**
     *      New array.
     *      @param children an ExtList with the children of this node 
     * (remove the ArrayInitializer out of the list).
     * @param init the arrayInitializer 
     * @param dimensions an int value.
     */

    public NewArray(ExtList children, KeYJavaType keyJavaType, 
		    ArrayInitializer init, int dimensions) {
	super(children);
	this.arrayInitializer = init;
        this.dimensions  = dimensions;
	this.keyJavaType = keyJavaType;
	assert dimensions > 0;	
    }
    
    
    /**
     *      New array.
     *      @param arguments an array of expressions describing the
     *        dimensions 
     * @param typeRef a reference to the arraytype
     * @param init the arrayInitializer 
     * @param dimensions an int value.
     */
    public NewArray(Expression[] arguments, TypeReference typeRef, 
		    KeYJavaType keyJavaType, ArrayInitializer init, 
		    int dimensions) {
	super(arguments, typeRef);
	this.arrayInitializer = init;
        this.dimensions  = dimensions;
	this.keyJavaType = keyJavaType;
	assert dimensions > 0;
    }

    public SourceElement getLastElement() {
        if (arrayInitializer != null) {
            return arrayInitializer;
        }
        return this;
    }
    
    /**
 *      Get arity.
 *      @return the int value.
     */

    public int getArity() {
        return 0;
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
        return PREFIX;
    }


    /**
 *      Get dimensions.
 *      @return the int value.
     */

    public int getDimensions() {
        return dimensions;
    }

    /**
 *      Get array initializer.
 *      @return the array initializer.
     */

    public ArrayInitializer getArrayInitializer() {
        return arrayInitializer;
    }

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (typeReference    != null) result++;
        if (children         != null) result += children.size();
        if (arrayInitializer != null) result++;
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
        if (typeReference != null) {
            if (index == 0) return typeReference;
            index--;
        }
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (arrayInitializer != null) {
            if (index == 0) return arrayInitializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get the number of expressions in this container.
 *      @return the number of expressions.
     */

    public int getExpressionCount() {
        int result = 0;
        if (children         != null) result += children.size();
        if (arrayInitializer != null) result++;
        return result;
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
        int len;
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (arrayInitializer != null) {
            if (index == 0) return arrayInitializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnNewArray(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printNewArray(this);
    }

    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
	return null;
    }

    /**
     * same as getKeYJavaType()
     */
    public KeYJavaType getKeYJavaType(Services javaServ) {
	return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType() {
	return keyJavaType;
    }
    
}