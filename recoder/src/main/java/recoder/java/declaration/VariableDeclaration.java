/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import java.util.List;

import recoder.java.SourceElement;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

/**
 * Variable declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class VariableDeclaration extends JavaDeclaration
        implements TypeReferenceContainer {

    /**
     * Type reference.
     */

    protected TypeReference typeReference;

    /**
     * Variable declaration.
     */

    public VariableDeclaration() {
        // nothing to do here
    }

    /**
     * Variable declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param vars a variable specification mutable list.
     */

    public VariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Variable declaration.
     *
     * @param proto a variable declaration.
     */

    protected VariableDeclaration(VariableDeclaration proto) {
        super(proto);
        if (proto.typeReference != null) {
            typeReference = proto.typeReference.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
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

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
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
     * @param t a type reference.
     */

    public void setTypeReference(TypeReference t) {
        typeReference = t;
    }

    /**
     * Get variables. WARNING: as of 0.80 final, this is not a mutable list any more due to
     * implementation of ParameterDeclaration - changes on this list don't have effects there!!
     *
     * @return the variable specification mutable list.
     */

    public abstract List<? extends VariableSpecification> getVariables();

    /**
     * Test whether the declaration is final.
     */

    public boolean isFinal() {
        return super.isFinal();
    }
}
