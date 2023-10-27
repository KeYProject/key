/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Variable declaration. taken from COMPOST and changed to achieve an immutable structure
 */

public abstract class VariableDeclaration extends JavaDeclaration
        implements TypeReferenceContainer {

    /**
     * Type reference.
     */

    protected final TypeReference typeReference;

    /**
     * this field stores if parent is an InterfaceDeclaration because we will be unable to walk the
     * tree upwards to check this
     */
    protected final boolean parentIsInterfaceDeclaration;


    /**
     * Variable declaration.
     */

    public VariableDeclaration() {
        typeReference = null;
        parentIsInterfaceDeclaration = false;
    }

    /**
     * Variable declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param parentIsInterfaceDeclaration a boolean set true iff the parent is an
     *        InterfaceDeclaration
     */
    public VariableDeclaration(Modifier[] mods, TypeReference typeRef,
            boolean parentIsInterfaceDeclaration) {
        super(mods);
        typeReference = typeRef;
        this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
    }

    /**
     * Variable declaration.
     *
     * @param mods a modifier immutable list.
     * @param typeRef a type reference.
     * @param parentIsInterfaceDeclaration a boolean set true iff the parent is an
     *        InterfaceDeclaration
     */
    public VariableDeclaration(ImmutableArray<Modifier> mods, TypeReference typeRef,
            boolean parentIsInterfaceDeclaration) {
        super(mods);
        typeReference = typeRef;
        this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
    }

    /**
     * Variable declaration.
     *
     * @param children an ExtList of children. May include: a TypeReference (as reference to the
     *        type of the declared variable) several Modifier (taken as modifiers of the
     *        declaration), Comments
     * @param parentIsInterfaceDeclaration a boolean set true iff the parent is an
     *        InterfaceDeclaration
     */
    public VariableDeclaration(ExtList children, boolean parentIsInterfaceDeclaration) {
        super(children);
        typeReference = children.get(TypeReference.class);
        this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
    }

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return getChildAt(0).getFirstElementIncludingBlocks();
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
     * array.
     *
     * @param index an index for a type reference.
     *
     * @return the type reference with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
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
     * Get variables.
     *
     * @return the variable specification array wrapper
     */

    public abstract ImmutableArray<? extends VariableSpecification> getVariables();

    /**
     * Test whether the declaration is final.
     */

    public boolean isFinal() {
        return super.isFinal();
    }

    /**
     * this field stores if parent is an InterfaceDeclaration because we will be unable to walk the
     * tree upwards to check this
     */
    public boolean parentIsInterfaceDeclaration() {
        return parentIsInterfaceDeclaration;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnVariableDeclaration(this);
    }
}
