/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;

/**
 * Instanceof.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Instanceof extends TypeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6100795662310024426L;

    /**
     * Instanceof.
     */

    public Instanceof() {
        // nothing to do
    }

    /**
     * Instanceof.
     *
     * @param child an expression.
     * @param typeref a type reference.
     */

    public Instanceof(Expression child, TypeReference typeref) {
        super(child, typeref);
        makeParentRoleValid();
    }

    /**
     * Instanceof.
     *
     * @param proto an instanceof.
     */

    protected Instanceof(Instanceof proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Instanceof deepClone() {
        return new Instanceof(this);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (children != null) {
            result += children.size();
        }
        if (typeReference != null) {
            result++;
        }
        return result;
    }

    public SourceElement getLastElement() {
        return typeReference.getLastElement();
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
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
            index--;
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
        return 5;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return POSTFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitInstanceof(this);
    }
}
