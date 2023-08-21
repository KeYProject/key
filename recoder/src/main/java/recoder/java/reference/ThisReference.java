/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * A reference to the current object. "this" can be prefixed by a type reference (to resolve
 * ambiguities with inner classes).
 */

public class ThisReference extends JavaNonTerminalProgramElement
        implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6068045198408155115L;

    /**
     * Expression parent.
     */
    protected ExpressionContainer expressionParent;

    /**
     * Reference parent.
     */
    protected ReferenceSuffix referenceParent;

    /**
     * Prefix.
     */
    protected TypeReference prefix;

    /**
     * This reference.
     */
    public ThisReference() {
        makeParentRoleValid();
    }

    /**
     * This reference.
     *
     * @param outer a type reference.
     */

    public ThisReference(TypeReference outer) {
        setReferencePrefix(outer);
        makeParentRoleValid();
    }

    /**
     * This reference.
     *
     * @param proto a this reference.
     */

    protected ThisReference(ThisReference proto) {
        super(proto);
        if (proto.prefix != null) {
            prefix = proto.prefix.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ThisReference deepClone() {
        return new ThisReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (prefix != null) {
            prefix.setReferenceSuffix(this);
        }
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else {
            return referenceParent;
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (prefix != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (prefix != null) {
            if (index == 0) {
                return prefix;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        if (prefix == child) {
            return 0;
        }
        return -1;
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
        if (prefix == p) {
            TypeReference r = (TypeReference) q;
            prefix = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Set reference prefix.
     *
     * @param x a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix x) {
        this.prefix = (TypeReference) x;
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return referenceParent;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        referenceParent = path;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (prefix != null) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeReference getTypeReferenceAt(int index) {
        if (prefix != null && index == 0) {
            return prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitThisReference(this);
    }
}
