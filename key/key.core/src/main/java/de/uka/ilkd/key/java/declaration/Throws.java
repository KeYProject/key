// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.util.List;

public class Throws extends JavaNonTerminalProgramElement implements TypeReferenceContainer {

    /**
     * Exceptions.
     */
    @Nonnull
    protected final ImmutableArray<TypeReference> exceptions;

    public Throws(PositionInfo pi, List<Comment> comments, @Nonnull ImmutableArray<TypeReference> exceptions) {
        super(pi, comments);
        this.exceptions = exceptions;
    }

    /**
     * Throws.
     *
     * @param exception a type reference.
     */
    public Throws(TypeReference exception) {
        this(null, null, new ImmutableArray<>(exception));
    }

    /**
     * Throws.
     *
     * @param list a type reference array.
     */
    public Throws(TypeReference[] list) {
        this(null, null, new ImmutableArray<>(list));
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain:
     *                 several of TypeReference (as references to thrown exceptions),
     *                 Comments
     */
    public Throws(ExtList children) {
        super(children);
        this.exceptions = new ImmutableArray<>(children.collect(TypeReference.class));
    }

    @Override
    @Nonnull
    public SourceElement getLastElement() {
        return exceptions.get(exceptions.size() - 1);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int result = 0;
        result += exceptions.size();
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                                        of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        return exceptions.get(index);
    }

    /**
     * Get exceptions.
     *
     * @return the type reference mutable list.
     */
    @Nonnull
    public ImmutableArray<TypeReference> getExceptions() {
        return exceptions;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    @Override
    public int getTypeReferenceCount() {
        return exceptions.size();
    }

    /*
      Return the type reference at the specified index in this node's
      "virtual" type reference array.
      @param index an index for a type reference.
      @return the type reference with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    @Override
    public TypeReference getTypeReferenceAt(int index) {
        return exceptions.get(index);
    }


    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnThrows(this);
    }


    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThrows(this);
    }
}