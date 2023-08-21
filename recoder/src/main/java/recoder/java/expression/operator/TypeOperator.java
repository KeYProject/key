/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.expression.Operator;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;

/**
 * Type operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class TypeOperator extends Operator implements TypeReferenceContainer {

    /**
     * Type reference.
     */
    protected TypeReference typeReference;

    /**
     * Type operator.
     */
    public TypeOperator() {
        // nothing to do
    }

    /**
     * Type operator.
     *
     * @param unaryChild an expression.
     * @param typeref a type reference.
     */
    public TypeOperator(Expression unaryChild, TypeReference typeref) {
        super(unaryChild);
        setTypeReference(typeref);
    }

    /**
     * Type operator.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     * @param typeref a type reference.
     */
    public TypeOperator(Expression lhs, Expression rhs, TypeReference typeref) {
        super(lhs, rhs);
        setTypeReference(typeref);
    }

    /**
     * Type operator.
     *
     * @param proto a type operator.
     */
    protected TypeOperator(TypeOperator proto) {
        super(proto);
        if (proto.typeReference != null) {
            typeReference = proto.typeReference.deepClone();
        }
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (typeReference != null) {
            typeReference.setParent(this);
        }
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): subexpression
        // role 1: type reference (for type operators only)
        // role 2: prefix (for New only)
        // role 3 (IDX): parameter (for New only)
        // role 4: class declaration (for New only)
        if (children != null) {
            int index = children.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (typeReference == child) {
            return 1;
        }
        return -1;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (typeReference != null) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (typeReference != null && index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        int count;
        count = (children == null) ? 0 : children.size();
        for (int i = 0; i < count; i++) {
            if (children.get(i) == p) {
                if (q == null) {
                    children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (typeReference == p) {
            TypeReference r = (TypeReference) q;
            typeReference = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }

        return false;
    }

    /**
     * Get type reference.
     *
     * @return the type reference.
     */

    public TypeReference getTypeReference() {
        return typeReference;
    }

    /**
     * Set type reference.
     *
     * @param t a type reference.
     */

    public void setTypeReference(TypeReference t) {
        typeReference = t;
    }
}
