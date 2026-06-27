/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a sequence of terms (antecedent or succulent).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * seq: term (COMMA term)*;
 * }</pre>
 */
@NullMarked
public class Seq extends BaseAstNode {
    private final List<Term> terms;

    public Seq(Position position, List<Term> terms) {
        super(position);
        this.terms = terms;
        for (Term t : terms) {
            setChildParent(t);
        }
    }

    public List<Term> getTerms() {
        return terms;
    }
}