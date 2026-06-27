/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a parallel term (multiple updates in parallel).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * parallel_term: (elementary_update_term (COMMA elementary_update_term)*)?;
 * }</pre>
 */
@NullMarked
public class ParallelTerm extends BaseAstNode {
    private final List<ElementaryUpdateTerm> updates;

    public ParallelTerm(Position position, List<ElementaryUpdateTerm> updates) {
        super(position);
        this.updates = updates;
        for (ElementaryUpdateTerm u : updates) {
            setChildParent(u);
        }
    }

    public List<ElementaryUpdateTerm> getUpdates() {
        return updates;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}