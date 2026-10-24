/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.reference;

import java.util.Objects;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Array length reference. As a length reference is int-valued, and hence it is no valid prefix. Do
 * <b>not</b> instantiate this class if you want to construct the Java expression
 * <code>a.length</code>! Use {@link JavaInfo#getArrayLength()} instead.
 */

@NullMarked
public class ArrayLengthReference extends JavaNonTerminalProgramElement
        implements Reference, Expression, ReferenceSuffix {


    /**
     * Reference prefix. It must evaluate to an ArrayType.
     */
    protected final @Nullable ReferencePrefix prefix;

    /**
     * Array length reference.
     */
    public ArrayLengthReference() {
        prefix = null;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: a
     *        ReferencePrefix (for the array length), Comments
     */
    public ArrayLengthReference(ExtList children) {
        super(children);
        prefix = children.get(ReferencePrefix.class);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (prefix != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (prefix != null && index == 0) {
            return prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return Objects.requireNonNull(javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT),
            "no KeYJavaType for int");
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getKeYJavaType(javaServ);
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */
    public @Nullable ReferencePrefix getReferencePrefix() {
        return prefix;
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
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnArrayLengthReference(this);
    }

}
