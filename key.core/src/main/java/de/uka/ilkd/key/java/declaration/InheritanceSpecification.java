/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Inheritance specification.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class InheritanceSpecification extends JavaNonTerminalProgramElement
        implements TypeReferenceContainer {

    /**
     * Supertypes.
     */

    protected final ImmutableArray<TypeReference> supertypes;


    /**
     * Inheritance specification.
     */

    public InheritanceSpecification() {
        this.supertypes = null;
    }

    /**
     * Inheritance specification.
     *
     * @param supertype a type reference.
     */

    public InheritanceSpecification(TypeReference supertype) {
        this.supertypes = new ImmutableArray<>(supertype);
    }

    /**
     * Inheritance specification.
     *
     * @param supertypes a type reference mutable list.
     */

    public InheritanceSpecification(TypeReference[] supertypes) {
        this.supertypes = new ImmutableArray<>(supertypes);
    }

    /**
     * Inheritance specification.
     *
     * @param children the ExtList may include: a Comment several TypeReference (as references to
     *        the supertypes) a Comment
     */
    protected InheritanceSpecification(ExtList children) {
        super(children);
        this.supertypes = new ImmutableArray<>(children.collect(TypeReference.class));
    }


    public SourceElement getLastElement() {
        if (supertypes == null) {
            return this;
        }
        return supertypes.get(supertypes.size() - 1);
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (supertypes != null) {
            result += supertypes.size();
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
        if (supertypes != null) {
            return supertypes.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get supertypes.
     *
     * @return the type reference array wrapper.
     */

    public ImmutableArray<TypeReference> getSupertypes() {
        return supertypes;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (supertypes != null) ? supertypes.size() : 0;
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
        if (supertypes != null) {
            return supertypes.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }
}
