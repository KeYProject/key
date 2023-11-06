/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;


/**
 * An ArrayInitializer is a valid expression exclusively for initializing ArrayTypes. Any other
 * expressions are suited for any expression node. These rules could have been expressed by
 * appropriate types, but these solutions would require a couple of new interfaces which did not
 * seem adequate. The parent expression is either another ArrayInitializer (nested blocks) or a
 * VariableDeclaration.
 */
public class ArrayInitializer extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {


    protected final ImmutableArray<Expression> children;
    protected final KeYJavaType kjt;

    /**
     * Array initializer.
     *
     * @param list with all children. May contain: several of Expression (as the initializing
     *        expression) Comments
     */
    public ArrayInitializer(ExtList list, KeYJavaType kjt) {
        super(list);
        assert kjt != null;
        this.kjt = kjt;
        this.children = new ImmutableArray<>(list.collect(Expression.class));
    }


    /**
     * create a new array initializer with the given expressions as elements.
     *
     * @param expressions a list of all contained elements
     */
    public ArrayInitializer(Expression[] expressions, KeYJavaType kjt) {
        super();
        assert kjt != null;
        this.kjt = kjt;
        this.children = new ImmutableArray<>(expressions);
    }


    @Override
    public int getChildCount() {
        return (children != null) ? children.size() : 0;
    }


    @Override
    public ProgramElement getChildAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    @Override
    public int getExpressionCount() {
        return (children != null) ? children.size() : 0;
    }


    @Override
    public Expression getExpressionAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnArrayInitializer(this);
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
