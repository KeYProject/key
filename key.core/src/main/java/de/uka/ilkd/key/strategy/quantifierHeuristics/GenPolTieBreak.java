/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.TreeSet;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;

/**
 * Orders tied instantiation candidates primarily by generation, that is by how late the
 * instance's newest skolem constant was introduced on the branch, and breaks a same-generation
 * tie by the proving-polarity occurrence connection of {@link PolarityOccurrenceTieBreak}.
 */
final class GenPolTieBreak extends PolarityOccurrenceTieBreak {

    static final GenPolTieBreak INSTANCE = new GenPolTieBreak();

    private GenPolTieBreak() {
    }

    @Override
    public Scorer prepare(View view) {
        final OccData occ = computeOccData(view);
        final Map<Term, Integer> gen = computeGenerationRanks(view);
        return inst -> generationValue(gen, inst) * (CAP + 1) + polarityValue(occ, inst);
    }

    /**
     * The generation rank of an instance: the introduction step of its newest skolem constant, or
     * {@link #CAP} if the instance is not among the ranked candidates.
     *
     * @param ranks the rank per candidate
     * @param inst the candidate instance
     * @return the generation rank
     */
    private static long generationValue(Map<Term, Integer> ranks, Term inst) {
        Integer rank = ranks.get(inst);
        if (rank == null && (inst.op() instanceof ParametricFunctionInstance pfi
                && pfi.getBase().name().equals(JavaDLTheory.CAST_NAME))) {
            rank = ranks.get(inst.sub(0));
        }
        return rank == null ? CAP : rank;
    }

    /**
     * Ranks every candidate instance by the introduction step of its newest skolem constant.
     *
     * @param view the instantiation view
     * @return the rank per candidate
     */
    private static Map<Term, Integer> computeGenerationRanks(View view) {
        final Map<Term, Integer> intro = new LinkedHashMap<>();
        final TreeSet<Integer> distinct = new TreeSet<>();
        final ArrayDeque<Term> todo = new ArrayDeque<>();
        for (final Term cand : view.candidates()) {
            int max = -1;
            todo.push(cand);
            while (!todo.isEmpty()) {
                final Term t = todo.pop();
                if (t.op() instanceof Function f && f.isSkolemConstant()) {
                    max = Math.max(max, f.introductionTime());
                }
                for (int i = 0; i < t.arity(); i++) {
                    todo.push(t.sub(i));
                }
            }
            intro.put(cand, max);
            if (max >= 0) {
                distinct.add(max);
            }
        }
        // ranks: generation zero -> 0, then 1, 2, ... in introduction order
        final Map<Integer, Integer> rankOf = new HashMap<>();
        int r = 1;
        for (final Integer step : distinct) {
            rankOf.put(step, Math.min(r++, CAP));
        }
        final Map<Term, Integer> ranks = new LinkedHashMap<>();
        for (final var e : intro.entrySet()) {
            ranks.put(e.getKey(), e.getValue() < 0 ? 0 : rankOf.get(e.getValue()));
        }
        return ranks;
    }
}
