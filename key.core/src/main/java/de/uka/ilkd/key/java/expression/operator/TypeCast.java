/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;


/**
 * Type cast.
 *
 */

public class TypeCast extends TypeOperator {

    /**
     * Type cast.
     */

    public TypeCast() {}

    /**
     * Note: The ordering of the arguments does not match the syntactical appearance of a Java type
     * case, but the order in the superclass TypeOperator. However, getASTChildren yields them in
     * the right order.
     */
    public TypeCast(Expression child, TypeReference typeref) {
        super(child, typeref);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     */
    public TypeCast(ExtList children) {
        super(children);
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (typeReference != null) {
            result++;
        }
        if (children != null) {
            result += children.size();
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        int len;
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
            index--;
        }
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
     * Checks if this operator is left or right associative. Type casts are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnTypeCast(this);
    }
}
