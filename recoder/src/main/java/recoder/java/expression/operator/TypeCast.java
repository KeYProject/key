/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;

/**
 * Type cast.
 *
 * @author <TT>AutoDoc</TT>
 */

public class TypeCast extends TypeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2209252813347809519L;

    /**
     * Type cast.
     */

    public TypeCast() {
        // nothing to do
    }

    /**
     * Note: The ordering of the arguments does not match the syntactical appearance of a Java type
     * case, but the order in the superclass TypeOperator. However, getASTChildren yields them in
     * the right order.
     */

    public TypeCast(Expression child, TypeReference typeref) {
        super(child, typeref);
        makeParentRoleValid();
    }

    /**
     * Type cast.
     *
     * @param proto a type cast.
     */

    protected TypeCast(TypeCast proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public TypeCast deepClone() {
        return new TypeCast(this);
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
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
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
            index -= len;
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
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>
     * false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitTypeCast(this);
    }
}
