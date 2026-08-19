/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;

/**
 * Instanceof with pattern matching (Java 16+).
 * Supports syntax: expr instanceof Type varName
 * where varName is bound as a local variable in the true branch.
 */
@NullMarked
public class InstanceofPattern extends TypeOperator {
    protected final VariableSpecification patternVariable;

    public InstanceofPattern(ExtList children) {
        super(children);
        this.patternVariable =
            Objects.requireNonNull(children.get(VariableSpecification.class));
    }

    public InstanceofPattern(Expression lhs, TypeReference type, VariableSpecification patternVar) {
        super(lhs, type);
        this.patternVariable = Objects.requireNonNull(patternVar);
    }

    public InstanceofPattern(PositionInfo pi, List<Comment> c, Expression lhs, TypeReference type,
            VariableSpecification patternVar) {
        super(pi, c, new ImmutableArray<>(lhs), type);
        this.patternVariable = Objects.requireNonNull(patternVar);
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
        return patternVariable;
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
            case 2 -> patternVariable;
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
     * Get the pattern variable bound by this instanceof expression.
     *
     * @return the VariableSpecification for the pattern variable, or null if no pattern
     */
    public VariableSpecification getPatternVariable() {
        return patternVariable;
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
