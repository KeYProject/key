/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a goal specification (find clause in taclet).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * goal_spec: term_or_seq;
 * }</pre>
 */
@NullMarked
public class GoalSpec extends BaseAstNode {
    private final TermOrSeq termOrSeq;

    public GoalSpec(Position position, TermOrSeq termOrSeq) {
        super(position);
        this.termOrSeq = termOrSeq;
        setChildParent(termOrSeq);
    }

    public TermOrSeq getTermOrSeq() {
        return termOrSeq;
    }
}