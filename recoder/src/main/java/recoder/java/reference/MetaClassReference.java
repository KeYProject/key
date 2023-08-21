/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * Meta class reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class MetaClassReference extends JavaNonTerminalProgramElement
        implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8591872994615086270L;

    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;

    /**
     * Reference parent.
     */

    protected ReferenceSuffix referenceParent;

    /**
     * Type reference.
     */

    protected TypeReference typeReference;

    /**
     * Meta class reference.
     */

    public MetaClassReference() {
        // nothing to do
    }

    /**
     * Meta class reference.
     *
     * @param reference a type reference.
     */

    public MetaClassReference(TypeReference reference) {
        setTypeReference(reference);
        makeParentRoleValid();
    }

    /**
     * Meta class reference.
     *
     * @param proto a meta class reference.
     */

    protected MetaClassReference(MetaClassReference proto) {
        super(proto);
        if (proto.typeReference != null) {
            typeReference = proto.typeReference.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public MetaClassReference deepClone() {
        return new MetaClassReference(this);
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

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (referenceParent != null) {
            return referenceParent;
        } else {
            return expressionParent;
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (typeReference != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        if (typeReference == child) {
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
        if (typeReference == p) {
            TypeReference r = (TypeReference) q;
            typeReference = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        return false;
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
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return typeReference;
    }

    /**
     * Set reference prefix.
     *
     * @param accessPath a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix accessPath) {
        typeReference = (TypeReference) accessPath;
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
     * @param ref a type reference.
     */

    public void setTypeReference(TypeReference ref) {
        typeReference = ref;
    }

    public SourceElement getFirstElement() {
        return (typeReference == null) ? this : typeReference.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitMetaClassReference(this);
    }
}
