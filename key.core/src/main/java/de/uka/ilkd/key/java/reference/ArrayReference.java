/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Array reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ArrayReference extends JavaNonTerminalProgramElement implements Reference, Expression,
        ReferencePrefix, ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {


    /**
     * Access path.
     */
    protected final ReferencePrefix prefix;


    /**
     * Inits.
     */
    protected final ImmutableArray<Expression> inits;


    /**
     * Array reference.
     */
    public ArrayReference() {
        prefix = null;
        this.inits = null;
    }

    /**
     * Array reference.
     *
     * @param accessPath a reference prefix.
     * @param initializers an expression array.
     */
    public ArrayReference(ReferencePrefix accessPath, Expression[] initializers) {
        this.prefix = accessPath;
        this.inits = new ImmutableArray<>(initializers);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: several of
     *        Expression (as initializers of the array), Comments. MUST NOT CONTAIN: the
     *        ReferencePrefix for the accessPath because Expression and ReferencePrefix might not be
     *        disjunct.
     * @param accessPath a ReferencePrefix of the array reference.
     */
    public ArrayReference(ExtList children, ReferencePrefix accessPath, PositionInfo pi) {
        super(children, pi);
        Expression[] e = children.collect(Expression.class);
        if (e.length > 1) {
            Expression[] e1 = new Expression[e.length - 1];
            System.arraycopy(e, 0, e1, 0, e1.length);
            this.prefix = new ArrayReference(e1, accessPath);
            e1 = new Expression[1];
            e1[0] = e[e.length - 1];
            this.inits = new ImmutableArray<>(e1);
        } else {
            this.prefix = accessPath;
            this.inits = new ImmutableArray<>(e);
        }
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: several of
     *        Expression (as initializers of the array), Comments. MUST NOT CONTAIN: the
     *        ReferencePrefix for the accessPath because Expression and ReferencePrefix might not be
     *        disjunct.
     * @param accessPath a ReferencePrefix of the array reference.
     */
    public ArrayReference(ExtList children, ReferencePrefix accessPath) {
        this(children, accessPath, children.get(PositionInfo.class));
    }

    private ArrayReference(Expression[] e, ReferencePrefix accessPath) {
        Expression[] e1 = new Expression[e.length - 1];
        if (e.length > 1) {
            System.arraycopy(e, 0, e1, 0, e1.length);
            this.prefix = new ArrayReference(e1, accessPath);
            e1[0] = e[e.length - 1];
            this.inits = new ImmutableArray<>(e1);
        } else {
            this.prefix = accessPath;
            this.inits = new ImmutableArray<>(e);
        }
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        int c = 0;
        if (prefix instanceof Expression) {
            c += 1;
        }
        if (inits != null) {
            c += inits.size();
        }
        return c;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     *
     * @return the expression with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression) {
            if (index == 0) {
                return (Expression) prefix;
            }
            index--;
        }
        if (inits != null) {
            return inits.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
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
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (prefix != null) {
            result++;
        }
        if (inits != null) {
            result += inits.size();
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
        if (prefix != null) {
            if (index == 0) {
                return prefix;
            }
            index--;
        }
        if (inits != null) {
            return inits.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get dimension expressions.
     *
     * @return the expression array wrapper.
     */
    public ImmutableArray<Expression> getDimensionExpressions() {
        return inits;
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (prefix == null) ? this : prefix.getFirstElementIncludingBlocks();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnArrayReference(this);
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        final KeYJavaType arrayType =
            services.getTypeConverter().getKeYJavaType((Expression) getChildAt(0), ec);
        return ((ArrayDeclaration) arrayType.getJavaType()).getBaseType().getKeYJavaType();
    }
}
