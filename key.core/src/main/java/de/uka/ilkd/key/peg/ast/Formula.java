/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a formula (wraps a Term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * formula: t=term;
 * }</pre>
 */
@NullMarked
public class Formula extends BaseAstNode {
    private final Term term;

    public Formula(Position position, Term term) {
        super(position);
        this.term = term;
        setChildParent(term);
    }

    public Term getTerm() {
        return term;
    }
}