/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Instanceof.
 */
public class Instanceof extends TypeOperator {
    public Instanceof(Expression unaryChild, TypeReference typeref) {
        super(unaryChild, typeref);
        assert this.getChildCount() == 2 : "not 2 children but " + this.getChildCount();
    }

    public Instanceof(PositionInfo pi, List<Comment> c, Expression lhs, TypeReference type) {
        super(pi, c, new ImmutableArray<>(lhs), type);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (children != null) {
            result += children.size();
        }
        if (typeReference != null) {
            result++;
        }
        return result;
    }

    public SourceElement getLastElement() {
        return typeReference;
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
        int len;
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 5;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return POSTFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnInstanceof(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getKeYJavaType(javaServ);
    }

}
