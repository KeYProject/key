/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a term in KeY logic.
 * Terms can be simple (literals, variables) or complex (quantified formulas, modalities, etc.)
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Term extends BaseAstNode {
    public enum TermType {
        PARALLEL,
        ELEMENTARY_UPDATE,
        EQUIVALENCE,
        IMPLICATION,
        DISJUNCTION,
        CONJUNCTION,
        NEGATION,
        QUANTIFIER,
        MODALITY,
        EQUALITY,
        COMPARISON,
        WEAK_ARITH,
        STRONG_ARITH_1,
        STRONG_ARITH_2,
        UPDATE,
        SUBSTITUTION,
        CAST,
        UNARY_MINUS,
        BRACKET,
        IF_THEN_ELSE,
        IF_EX_THEN_ELSE,
        LOCATION,
        LOCSET,
        ACCESS,
        ABBREVIATION,
        LITERAL
    }

    private final TermType type;
    private final String operator;
    private final @Nullable Term left;
    private final @Nullable Term right;
    private final @Nullable Term[] children;
    private final @Nullable BoundVariables boundVariables;
    private final @Nullable Label label;

    public Term(Position position,
                TermType type, String operator, @Nullable Term left, @Nullable Term right,
                @Nullable Term[] children, @Nullable BoundVariables boundVariables,
                @Nullable Label label) {
        super(position);
        this.type = type;
        this.operator = operator;
        this.left = left;
        this.right = right;
        this.children = children;
        this.boundVariables = boundVariables;
        this.label = label;

        setChildParent(left);
        setChildParent(right);
        if (children != null) {
            for (Term child : children) {
                setChildParent(child);
            }
        }
        setChildParent(boundVariables);
        setChildParent(label);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public TermType getType() {
        return type;
    }

    public String getOperator() {
        return operator;
    }

    public @Nullable Term getLeft() {
        return left;
    }

    public @Nullable Term getRight() {
        return right;
    }

    public @Nullable Term[] getChildren() {
        return children;
    }

    public @Nullable BoundVariables getBoundVariables() {
        return boundVariables;
    }

    public @Nullable Label getLabel() {
        return label;
    }

    public boolean isFormula() {
        switch (type) {
            case EQUIVALENCE:
            case IMPLICATION:
            case DISJUNCTION:
            case CONJUNCTION:
            case NEGATION:
            case QUANTIFIER:
            case MODALITY:
            case EQUALITY:
            case COMPARISON:
            case IF_THEN_ELSE:
            case IF_EX_THEN_ELSE:
                return true;
            default:
                return false;
        }
    }
}