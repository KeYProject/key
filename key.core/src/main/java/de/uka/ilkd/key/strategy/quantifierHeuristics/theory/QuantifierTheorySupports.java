/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.List;

/**
 * The theories the quantifier heuristic consults, in the order it consults them.
 *
 * A profile hands out the lists (see {@code Profile#getTheorySupports}), so a front end whose
 * terms are built from other theories registers its own instead of these. The order decides the
 * outcome where two theories both answer: a literal is decided by the first that reaches a
 * verdict, so equality comes before integer arithmetic, as in the original prover.
 */
public final class QuantifierTheorySupports {

    private QuantifierTheorySupports() {}

    /** Everything the heuristic knows about the terms of the Java front end. */
    public static final List<QuantifierTheorySupport> JAVA_DL =
        List.of(new HeapArrayTheorySupport(), new EqualityTheorySupport(),
            new IntegerTheorySupport());

    /**
     * The classic trigger selection: equality and integer rejection only, without the knowledge
     * about the heap. The strategy option {@code TRIGGERS_CLASSIC} selects it.
     */
    public static final List<QuantifierTheorySupport> CLASSIC =
        List.of(new EqualityTheorySupport(), new IntegerTheorySupport());
}
