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

public class SuperReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferencePrefix,
        ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {

    /**
     * Access path.
     */
    @Nullable
    private final ReferencePrefix prefix;


    public SuperReference(PositionInfo pi, List<Comment> comments, ReferencePrefix prefix) {
        super(pi, comments);
        this.prefix = prefix;
    }

    public SuperReference() {
        this(null, null, null);
    }

    /**
     * Super reference.
     *
     * @param accessPath a reference expression.
     */
    public SuperReference(ReferencePrefix accessPath) {
        this(null, null, accessPath);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     */
    public SuperReference(ExtList children) {
        super(children);
        prefix = children.get(ReferencePrefix.class);
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
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    @Override
    public ReferencePrefix getReferencePrefix() {
        return prefix;
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
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    @Override
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

    @Override
    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression && index == 0) {
            return (Expression) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    @Override
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

    @Override
    public TypeReference getTypeReferenceAt(int index) {
        if ((prefix instanceof TypeReference) && index == 0) {
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
        v.performActionOnSuperReference(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSuperReference(this);
    }

    /**
     * returns the KeYJavaType
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getSuperclass
                (ec.getTypeReference().getKeYJavaType());
    }

}