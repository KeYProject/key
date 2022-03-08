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
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;

/**
 * Occurs in a constructor declaration as the first statement
 * as this(...) or super(...) reference.
 * The Reference knows the constructor declaration it refers to.
 */

public abstract class SpecialConstructorReference
        extends JavaNonTerminalProgramElement implements ConstructorReference {

    @Nonnull
    protected final ImmutableArray<Expression> arguments;

    public SpecialConstructorReference(PositionInfo pi, List<Comment> comments,
                                       @Nullable ImmutableArray<Expression> arguments) {
        super(pi, comments);
        this.arguments = arguments == null ? new ImmutableArray<>() : arguments;
    }

    public SpecialConstructorReference() {
        this(null, null, null);
    }

    /**
     * Special constructor reference.
     *
     * @param arguments an expression mutable list.
     */
    public SpecialConstructorReference(Expression[] arguments) {
        this(null, null, new ImmutableArray<>(arguments));
    }


    /**
     * Special constructor reference.
     *
     * @param arguments an expression mutable list.
     */
    public SpecialConstructorReference(@Nullable ImmutableArray<Expression> arguments) {
        this(null, null, arguments);
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain:
     *                 several of Expression (as initializers of the array),
     *                 Comments
     */
    public SpecialConstructorReference(ExtList children) {
        super(children);
        this.arguments = new ImmutableArray<>(children.collect(Expression.class));
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain:
     *                 several of Expression (as initializers of the array),
     *                 Comments
     */
    public SpecialConstructorReference(ExtList children, PositionInfo pi) {
        super(children, pi);
        this.arguments = new ImmutableArray<>(children.collect(Expression.class));
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return getExpressionCount();
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
        return arguments.get(index);
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return arguments.size();
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
        return arguments.get(index);
    }

    /**
     * Get arguments.
     *
     * @return the expression mutable list.
     */
    public ImmutableArray<Expression> getArguments() {
        return arguments;
    }
}