/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a semi-sequent with antecedent and succulent.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * semi_sequent: ante=seq SEMI succ=seq;
 * }</pre>
 */
@NullMarked
public class SemiSequent extends BaseAstNode {
    private final Seq antecedent;
    private final Seq succulent;

    public SemiSequent(Position position, Seq antecedent, Seq succulent) {
        super(position);
        this.antecedent = antecedent;
        this.succulent = succulent;
        setChildParent(antecedent);
        setChildParent(succulent);
    }

    public Seq getAntecedent() {
        return antecedent;
    }

    public Seq getSucculent() {
        return succulent;
    }
}