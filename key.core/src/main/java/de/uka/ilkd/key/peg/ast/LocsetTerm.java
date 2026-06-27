/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a location set term (for heap operations).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * locset_term: LBRACE (term (COMMA term)*)? RBRACE;
 * }</pre>
 */
@NullMarked
public class LocsetTerm extends BaseAstNode {
    private final java.util.List<Term> locations;

    public LocsetTerm(Position position, java.util.List<Term> locations) {
        super(position);
        this.locations = locations;
        for (Term t : locations) {
            setChildParent(t);
        }
    }

    public java.util.List<Term> getLocations() {
        return locations;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}