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

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;

/**
 * A reference to the current object.
 * "this" can be prefixed by a type reference (to resolve ambiguities
 * with inner classes).
 */

public class ThisReference extends JavaNonTerminalProgramElement
        implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {

    @Nullable
    private final TypeReference prefix;

    public ThisReference(PositionInfo pi, List<Comment> comments, @Nullable TypeReference prefix) {
        super(pi, comments);
        this.prefix = prefix;
    }

    /**
     * This reference.
     */
    public ThisReference() {
        this(null, null, null);
    }

    /**
     * This reference.
     *
     * @param outer a type reference.
     */
    public ThisReference(TypeReference outer) {
        this(null, null, outer);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain:
     *                 a TypeReference (as reference for the ThisReference)
     *                 Comments
     */
    public ThisReference(ExtList children) {
        super(children);
        prefix = children.get(TypeReference.class);
    }


    @Override
    @Nonnull
    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (prefix == null) ? this : prefix.getFirstElementIncludingBlocks();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int count = 0;
        if (prefix != null) count++;
        return count;
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
        if (prefix != null) {
            if (index == 0) return prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */
    @Override
    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    @Override
    public int getTypeReferenceCount() {
        return (prefix != null) ? 1 : 0;
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
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnThisReference(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThisReference(this);
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ,
                                      ExecutionContext ec) {
        return ec.getTypeReference().getKeYJavaType();
    }

}