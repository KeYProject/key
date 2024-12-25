/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Throws.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Throws extends JavaNonTerminalProgramElement implements TypeReferenceContainer {
    /**
     * Exceptions thrown.
     */
    protected final ImmutableArray<TypeReference> exceptions;

    /**
     * Throws.
     */
    public Throws() {
        this(new TypeReference[0]);
    }

    /**
     * Throws.
     *
     * @param exception a type reference.
     */
    public Throws(TypeReference exception) {
        this(new TypeReference[]{exception});
    }

    /**
     * Throws.
     *
     * @param list a type reference array.
     */
    public Throws(TypeReference[] list) {
        this(null, null, new ImmutableArray<>(list));
    }

    public Throws(@Nullable PositionInfo pi, @Nullable List<Comment> c, ImmutableArray<TypeReference> exc) {
        super(pi, c);
        this.exceptions = exc;
    }

    public SourceElement getLastElement() {
        if (exceptions == null) {
            return this;
        }
        return exceptions.get(exceptions.size() - 1);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (exceptions != null) {
            result += exceptions.size();
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
        if (exceptions != null) {
            return exceptions.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get exceptions.
     *
     * @return the type reference mutable list.
     */
    public ImmutableArray<TypeReference> getExceptions() {
        return exceptions;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (exceptions != null) ? exceptions.size() : 0;
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
        if (exceptions != null) {
            return exceptions.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnThrows(this);
    }
}
