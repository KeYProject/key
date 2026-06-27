/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a brace suffix (anonymous object creation).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * brace_suffix: LBRACE (term (COMMA term)*)? RBRACE;
 * }</pre>
 */
@NullMarked
public class BraceSuffix extends BaseAstNode {
    private final java.util.List<Term> elements;

    public BraceSuffix(Position position, java.util.List<Term> elements) {
        super(position);
        this.elements = elements;
        for (Term t : elements) {
            setChildParent(t);
        }
    }

    public java.util.List<Term> getElements() {
        return elements;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}