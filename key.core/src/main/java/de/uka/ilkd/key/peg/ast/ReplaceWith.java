/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents replace-with clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * replace_with: term | LPAREN seq SEMI seq RPAREN;
 * }</pre>
 */
@NullMarked
public class ReplaceWith extends BaseAstNode {
    private final @Nullable Term term;
    private final @Nullable Seq antecedent;
    private final @Nullable Seq succulent;

    public ReplaceWith(Position position, Term term) {
        super(position);
        this.term = term;
        this.antecedent = null;
        this.succulent = null;
        setChildParent(term);
    }

    public ReplaceWith(Position position, Seq antecedent, Seq succulent) {
        super(position);
        this.term = null;
        this.antecedent = antecedent;
        this.succulent = succulent;
        setChildParent(antecedent);
        setChildParent(succulent);
    }

    public @Nullable Term getTerm() {
        return term;
    }

    public @Nullable Seq getAntecedent() {
        return antecedent;
    }

    public @Nullable Seq getSucculent() {
        return succulent;
    }

    public boolean isTerm() {
        return term != null;
    }
}