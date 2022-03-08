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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;


public class FieldReference extends VariableReference
        implements MemberReference, ReferenceSuffix, TypeReferenceContainer, ExpressionContainer {

    @Nullable
    private final ReferencePrefix prefix;

    public FieldReference(PositionInfo pi, List<Comment> comments, ProgramVariable variable, ReferencePrefix prefix) {
        super(pi, comments, variable);
        this.prefix = prefix;
    }

    public FieldReference(ProgramVariable variable, PositionInfo pi, ReferencePrefix prefix) {
        this(pi, null, variable, prefix);
    }

    protected FieldReference() {
        this(null, null, null, null);
    }

    public FieldReference(ProgramVariable pv, ReferencePrefix prefix) {
        this(null, null, pv, getPrefix(pv, prefix));
    }

    private static ReferencePrefix getPrefix(ProgramVariable pv, ReferencePrefix prefix) {
        if (prefix == null && !pv.isStatic() && pv.isMember()) {
            return new ThisReference();
        } else {
            return prefix;
        }
    }

    public FieldReference(ExtList children, ReferencePrefix prefix) {
        super(children);
        this.prefix = getPrefix(getProgramVariable(), prefix);
    }


    public FieldReference(ProgramVariable pv, ReferencePrefix prefix, PositionInfo pi) {
        this(pi, null, pv, getPrefix(pv, prefix));
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (prefix != null) result++;
        if (getProgramVariable() != null) result++;
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
    public ProgramElement getChildAt(int index) {
        if (prefix != null) {
            if (index == 0) return prefix;
            index--;
        }
        if (getProgramVariable() != null) {
            if (index == 0) return getProgramVariable();
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */
    @Nullable
    public final ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /*
     * returns true if the reference prefix is an explicit or implicit
     * this reference this field reference does not refer to a static field
     */
    public boolean referencesOwnInstanceField() {
        return (prefix == null || prefix instanceof ThisReference) &&
                !getProgramVariable().isStatic();
    }


    /**
     * Set reference prefix.
     *
     * @author VK
     */
    public ReferencePrefix setReferencePrefix(ReferencePrefix rp) {
        return new FieldReference(getProgramVariable(), rp);
    }


    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (prefix instanceof TypeReference) ? 1 : 0;
    }

    /*
      Return the type reference at the specified index in this node's
      "virtual" type reference array.
      @param index an index for a type reference.
      @return the type reference with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public TypeReference getTypeReferenceAt(int index) {
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (prefix instanceof Expression) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression && index == 0) {
            return (Expression) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Nonnull
    public SourceElement getFirstElement() {
        return (prefix == null) ? getProgramVariable() : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (prefix == null) ? getProgramVariable() : prefix.getFirstElementIncludingBlocks();
    }

    /**
     * pretty print
     */
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFieldReference(this);
    }


    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnFieldReference(this);
    }

    /**
     * are there "dots" in the prefix?
     */
    public boolean isSingleDeref() {
        return prefix.getReferencePrefix() == null;
    }

}