/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a substitution term (term[subst]).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * substitution_term: term LBRACKET subst RBRACKET;
 * }</pre>
 */
@NullMarked
public class SubstitutionTerm extends BaseAstNode {
    private final Term term;
    private final Term substitution;

    public SubstitutionTerm(Position position, Term term, Term substitution) {
        super(position);
        this.term = term;
        this.substitution = substitution;
        setChildParent(term);
        setChildParent(substitution);
    }

    public Term getTerm() {
        return term;
    }

    public Term getSubstitution() {
        return substitution;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}