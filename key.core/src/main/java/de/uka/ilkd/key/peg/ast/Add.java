/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents add clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * add: term;
 * }</pre>
 */
@NullMarked
public class Add extends BaseAstNode {
    private final Term term;

    public Add(Position position, Term term) {
        super(position);
        this.term = term;
        setChildParent(term);
    }

    public Term getTerm() {
        return term;
    }
}