/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;

/**
 * Instanceof with pattern matching (Java 16+).
 *
 * <p>
 * Supports both a type pattern ({@code expr instanceof Type varName}) and a record pattern
 * ({@code expr instanceof Record(int x, ...)}). The variables declared by the pattern are bound as
 * local variables where the pattern is definitely matched.
 *
 * @see Pattern
 * @see TypeOperator
 */
@NullMarked
public class InstanceofPattern extends TypeOperator {
    protected final Pattern pattern;

    public InstanceofPattern(ExtList children) {
        super(children);
        this.pattern = Objects.requireNonNull(children.get(Pattern.class));
    }

    public InstanceofPattern(Expression lhs, TypeReference type, Pattern pattern) {
        super(lhs, type);
        this.pattern = Objects.requireNonNull(pattern);
    }

    public InstanceofPattern(PositionInfo pi, List<Comment> c, Expression lhs, TypeReference type,
            Pattern pattern) {
        super(pi, c, new ImmutableArray<>(lhs), type);
        this.pattern = Objects.requireNonNull(pattern);
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

        result++;
        assert result == 3;
        return result;
    }

    public SourceElement getLastElement() {
        return pattern;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        return switch (index) {
            case 0 -> children.get(0);
            case 1 -> typeReference;
            case 2 -> pattern;
            default -> throw new IllegalStateException("Unexpected value: " + index);
        };
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
     * Get the pattern matched by this instanceof expression.
     *
     * @return the pattern, never {@code null}
     */
    public Pattern getPattern() {
        return pattern;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnInstanceofPattern(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getKeYJavaType(javaServ);
    }
}
