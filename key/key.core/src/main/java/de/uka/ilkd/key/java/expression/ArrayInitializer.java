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

package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.util.List;


/**
 * An ArrayInitializer is a valid expression exclusively for initializing
 * ArrayTypes. Any other expressions are suited for any expression node.
 * These rules could have been expressed by appropriate types, but these
 * solutions would require a couple of new interfaces which did not seem
 * adequate.
 * The parent expression is either another ArrayInitializer (nested blocks)
 * or a VariableDeclaration.
 */
public final class ArrayInitializer extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {

    @Nonnull
    private final ImmutableArray<Expression> children;

    @Nonnull
    private final KeYJavaType kjt;

    public ArrayInitializer(PositionInfo pi, List<Comment> comments,
                            @Nonnull ImmutableArray<Expression> children, @Nonnull KeYJavaType kjt) {
        super(pi, comments);
        this.children = children;
        this.kjt = kjt;
    }

    /**
     * Array initializer.
     *
     * @param list with all children.
     *             May contain:
     *             several of Expression (as the initializing expression)
     *             Comments
     */
    public ArrayInitializer(ExtList list, @Nonnull KeYJavaType kjt) {
        super(list);
        this.kjt = kjt;
        this.children = new ImmutableArray<>(list.collect(Expression.class));
    }


    /**
     * create a new array initializer with the given expressions as elements.
     *
     * @param expressions a list of all contained elements
     */
    public ArrayInitializer(Expression[] expressions, KeYJavaType kjt) {
        this(null, null, new ImmutableArray<>(expressions), kjt);
    }


    @Override
    public int getChildCount() {
        return children.size();
    }


    @Override
    public ProgramElement getChildAt(int index) {
        return children.get(index);
    }


    @Override
    public int getExpressionCount() {
        return children.size();
    }


    @Override
    public Expression getExpressionAt(int index) {
        return children.get(index);
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnArrayInitializer(this);
    }


    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printArrayInitializer(this);
    }


    /**
     * Get arguments.
     *
     * @return the wrapped argument array
     */
    public ImmutableArray<Expression> getArguments() {
        return children;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return kjt;
    }
}
