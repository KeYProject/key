/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;

/**
 * Orders tied instantiation candidates primarily by generation, that is by how late the
 * instance's newest skolem constant was introduced on the branch, and breaks a same-generation
 * tie by the
 * proving-polarity occurrence connection of {@link PolarityOccurrenceTieBreak}. The tie-break of
 * the {@code Good} quantifier treatment.
 *
 * Generation-primary keeps the sequent walk to a secondary role: it only decides between candidates
 * of the same generation, which for the input constants of generation zero is the one large group.
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
     * Ranks every candidate instance by the introduction step of its newest skolem constant. A
     * candidate whose symbols all come from the problem input ranks 0, like a generation zero term
     * of an SMT solver; the skolem-containing candidates follow in the order their newest symbol
     * was
     * introduced on the branch, capped by {@link #CAP}. All candidates' skolem constants are
     * resolved in one walk over the branch's rule applications.
     *
     * @param view the instantiation view
     * @return the rank per candidate
     */
    private static Map<Term, Integer> computeGenerationRanks(View view) {
        // the skolem constants occurring in each candidate
        final Map<Term, List<Operator>> skolems = new LinkedHashMap<>();
        final Set<Operator> wanted = new HashSet<>();
        final ArrayDeque<Term> todo = new ArrayDeque<>();
        for (final Term cand : view.candidates()) {
            final List<Operator> ops = new ArrayList<>(2);
            todo.push(cand);
            while (!todo.isEmpty()) {
                final Term t = todo.pop();
                if (t.op() instanceof Function f && f.isSkolemConstant()) {
                    ops.add(f);
                    wanted.add(f);
                }
                for (int i = 0; i < t.arity(); i++) {
                    todo.push(t.sub(i));
                }
            }
            skolems.put(cand, ops);
        }
        // one walk over the branch: the introduction step of every wanted skolem constant. Unlike
        // the introduction time of the arithmetic ordering this considers every taclet, so the
        // delta-rule skolems are found as well.
        final Map<Operator, Integer> steps = new HashMap<>();
        if (!wanted.isEmpty()) {
            final Goal goal = view.goal();
            ImmutableList<RuleApp> applied = goal.appliedRuleApps();
            while (!applied.isEmpty() && steps.size() < wanted.size()) {
                final RuleApp app = applied.head();
                applied = applied.tail();
                if (!(app instanceof TacletApp tapp)) {
                    continue;
                }
                for (final var entry : tapp.instantiations().getInstantiationMap()) {
                    if (!(entry.key() instanceof SkolemTermSV)) {
                        continue;
                    }
                    final Operator op = ((Term) entry.value().getInstantiation()).op();
                    if (wanted.contains(op)) {
                        steps.putIfAbsent(op, applied.size());
                    }
                }
            }
        }
        // newest skolem decides a candidate's introduction step; -1 = generation zero
        final Map<Term, Integer> intro = new LinkedHashMap<>();
        final TreeSet<Integer> distinct = new TreeSet<>();
        for (final var e : skolems.entrySet()) {
            int max = -1;
            for (final Operator op : e.getValue()) {
                max = Math.max(max, steps.getOrDefault(op, -1));
            }
            intro.put(e.getKey(), max);
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
