/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an update term (sequential composition).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * update_term: LBRACE elementary_update_term (SEMI elementary_update_term)* RBRACE;
 * }</pre>
 */
@NullMarked
public class UpdateTerm extends BaseAstNode {
    private final java.util.List<ElementaryUpdateTerm> updates;

    public UpdateTerm(Position position, java.util.List<ElementaryUpdateTerm> updates) {
        super(position);
        this.updates = updates;
        for (ElementaryUpdateTerm u : updates) {
            setChildParent(u);
        }
    }

    public java.util.List<ElementaryUpdateTerm> getUpdates() {
        return updates;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}