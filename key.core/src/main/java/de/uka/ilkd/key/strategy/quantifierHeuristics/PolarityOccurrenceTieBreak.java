/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * The shared machinery of the occurrence-based tie-breaks. Both {@link PolarityTieBreak} and the
 * secondary of {@link GenPolTieBreak} order candidates by how strongly an instance is connected to
 * the sequent, giving occurrences at proving polarity twice the weight. This base owns the walk
 * that produces those counts and the {@link #polarityValue} that reads them; the subclasses only
 * combine.
 *
 * The counts are collected per sequent formula: which operators occur in the formula, and which at
 * relative proving polarity. A sequent step replaces few formulas and the
 * {@link SequentFormula} objects are immutable and shared along a branch, so the per-formula
 * summary is memoised in {@link de.uka.ilkd.key.java.ServiceCaches}. The per-sequent aggregation is
 * memoised once more in a thread-local, so all quantified formulas of one sequent reuse it.
 */
abstract class PolarityOccurrenceTieBreak implements QuantifierInstantiationTieBreak {

    /** The largest tie-break value; an instance in this many or more formulas gets the value 0. */
    static final int CAP = 15;

    /**
     * The occurrence counts of a candidate set: formulas per instance, proving-polarity per
     * instance.
     */
    record OccData(Map<Term, Integer> occ, Map<Term, Integer> goalOcc) {
    }

    /**
     * Collects the occurrence counts of the view's candidates: for each candidate the number of
     * sequent formulas it occurs in, and for a constant candidate the number where it occurs at
     * proving polarity. Compound candidates are counted exactly, capped, in one walk shared by all.
     *
     * @param view the instantiation view
     * @return the occurrence counts
     */
    protected static OccData computeOccData(View view) {
        final Map<Term, Integer> occ = new LinkedHashMap<>();
        final Map<Term, Integer> goalOcc = new LinkedHashMap<>();
        final Collection<Term> candidates = view.candidates();
        if (candidates.isEmpty()) {
            return new OccData(occ, goalOcc);
        }
        final Sequent seq = view.sequent();
        final SequentCounts counts = sequentCounts(seq, view.services());
        final List<Term> unknown = new ArrayList<>();
        for (final Term cand : candidates) {
            if (cand.arity() == 0) {
                occ.put(cand, counts.opCounts().getOrDefault(cand.op(), 0));
                goalOcc.put(cand, counts.goalCounts().getOrDefault(cand.op(), 0));
            } else {
                final Integer known = counts.compoundCounts().get(cand);
                if (known != null) {
                    occ.put(cand, known);
                } else {
                    unknown.add(cand);
                }
            }
        }
        if (!unknown.isEmpty()) {
            countCompounds(seq, unknown, counts.compoundCounts());
            for (final Term cand : unknown) {
                // store a zero for candidates never found, so they are not counted again for the
                // next quantified formula of this sequent
                counts.compoundCounts().putIfAbsent(cand, 0);
                occ.put(cand, counts.compoundCounts().get(cand));
            }
        }
        return new OccData(occ, goalOcc);
    }

    /**
     * The occurrence value of an instance with the proving-polarity boost: a formula where the
     * instance occurs at proving polarity counts twice, so of two equally frequent instances the
     * one the proof still has to say something about comes first. A weakly connected instance gets
     * a
     * large value, a strongly connected one a small value, bounded by {@link #CAP}.
     *
     * @param d the occurrence counts
     * @param inst the candidate instance
     * @return the boosted occurrence value, between 0 and {@link #CAP}
     */
    protected static long polarityValue(OccData d, Term inst) {
        Integer occ = d.occ().get(inst);
        Integer pos = d.goalOcc().get(inst);
        if (occ == null && (inst.op() instanceof ParametricFunctionInstance pfi
                && pfi.getBase().name().equals(JavaDLTheory.CAST_NAME))) {
            occ = d.occ().get(inst.sub(0));
            pos = d.goalOcc().get(inst.sub(0));
        }
        if (occ == null) {
            return CAP;
        }
        final int boosted = occ + (pos == null ? 0 : pos);
        return Math.max(0, CAP - Math.min(boosted, CAP));
    }

    // ------------------------------------------------------------------------
    // the per-formula walk and its two caches
    // ------------------------------------------------------------------------

    /** Offset making a formula-layer polarity (-1, 0, +1) a non-negative walk state. */
    private static final int FORMULA_BASE = 1;
    /** Offset marking a frozen polarity; states at or above it no longer flip. */
    private static final int FROZEN_BASE = 4;

    /** The formula count per operator and the proving-polarity formula count per operator. */
    private record SequentCounts(Proof proof, Sequent seq, Map<Operator, Integer> opCounts,
            Map<Operator, Integer> goalCounts, Map<Term, Integer> compoundCounts) {
    }

    /**
     * The operator sets of a single sequent formula, all polarities relative to the formula root:
     * the operators occurring in it, and those occurring at relative proving polarity {@code +1}
     * respectively {@code -1} (in a non-connective position).
     */
    record OccInfo(Set<Operator> opsAny, Set<Operator> opsRelPlus,
            Set<Operator> opsRelMinus) {
    }

    /**
     * Per-thread single-entry cache for {@link #sequentCounts}, so all quantified formulas of one
     * sequent reuse the aggregation.
     */
    private static final ThreadLocal<SequentCounts> lastCounts = new ThreadLocal<>();

    /**
     * The occurrence knowledge of the sequent, aggregated from the per-formula summaries: the
     * number
     * of formulas each operator occurs in, and the number where it occurs at proving polarity
     * (succedent at relative {@code +1}, antecedent at relative {@code -1}).
     */
    private static SequentCounts sequentCounts(Sequent seq, Services services) {
        final Proof proof = services.getProof();
        final SequentCounts cached = lastCounts.get();
        if (cached != null && cached.seq() == seq) {
            return cached;
        }
        if (cached != null && proof != cached.proof()) {
            // The memo belongs to another proof. Drop it before computing, so the other
            // proof's sequent stays reachable only while this entry is in use.
            lastCounts.remove();
        }
        final Map<Operator, Integer> counts = new HashMap<>();
        final Map<Operator, Integer> goal = new HashMap<>();
        boolean antec = true;
        int rows = seq.antecedent().size();
        for (final SequentFormula cf : seq) {
            if (rows-- == 0) {
                antec = false;
            }
            final OccInfo info = occInfo(cf, services);
            for (final Operator op : info.opsAny()) {
                counts.merge(op, 1, Integer::sum);
            }
            for (final Operator op : antec ? info.opsRelMinus() : info.opsRelPlus()) {
                goal.merge(op, 1, Integer::sum);
            }
        }
        final SequentCounts result =
            new SequentCounts(proof, seq, counts, goal, new LinkedHashMap<>());
        lastCounts.set(result);
        return result;
    }

    /**
     * The operator summary of a sequent formula, computed once per formula and cached. The walk
     * pairs each subterm with its polarity relative to the formula root, following the rules of the
     * taclet application restrictions: the root is proving ({@code +1}), a negation and the left
     * side of an implication flip, conjunction, disjunction, the right side of an implication and
     * the branches of a conditional keep, everything else (equivalences, quantifiers, modalities)
     * is
     * neutral. The polarity is frozen when the walk enters an atom. State encoding: polarity+1 for
     * the formula layer, polarity+4 once frozen.
     */
    /** The walk state of a formula-layer position: the polarity shifted to be non-negative. */
    private static int formulaState(int polarity) {
        return polarity + FORMULA_BASE;
    }

    /** The walk state below an atom: the polarity is frozen and no longer flips. */
    private static int frozenState(int polarity) {
        return polarity + FROZEN_BASE;
    }

    static OccInfo occInfo(SequentFormula cf, Services services) {
        final Map<SequentFormula, Object> cache = services.getCaches().getFormulaOccurrenceCache();
        final Object hit = cache.get(cf);
        if (hit != null) {
            return (OccInfo) hit;
        }
        final Set<Operator> opsAny = new HashSet<>();
        final Set<Operator> relPlus = new HashSet<>();
        final Set<Operator> relMinus = new HashSet<>();
        final ArrayDeque<Term> todo = new ArrayDeque<>();
        final ArrayDeque<Integer> todoState = new ArrayDeque<>();
        final Map<Term, Integer> visitedMask = new HashMap<>();
        todo.push(cf.formula());
        todoState.push(formulaState(1));
        while (!todo.isEmpty()) {
            final Term t = todo.pop();
            final int state = todoState.pop();
            final Integer seen = visitedMask.get(t);
            final int bit = 1 << state;
            if (seen != null && (seen & bit) != 0) {
                continue;
            }
            visitedMask.put(t, seen == null ? bit : seen | bit);
            final boolean frozen = state >= frozenState(-1);
            final int pol = frozen ? state - FROZEN_BASE : state - FORMULA_BASE;
            final Operator op = t.op();
            opsAny.add(op);
            if (frozen || !isConnective(op)) {
                if (pol == 1) {
                    relPlus.add(op);
                } else if (pol == -1) {
                    relMinus.add(op);
                }
            }
            for (int i = 0; i < t.arity(); i++) {
                final int childState;
                if (frozen) {
                    childState = state;
                } else if (op == Junctor.NOT || (op == Junctor.IMP && i == 0)) {
                    childState = formulaState(-pol);
                } else if (op == Junctor.AND || op == Junctor.OR
                        || (op == Junctor.IMP && i != 0)) {
                    childState = formulaState(pol);
                } else if (op == IfThenElse.IF_THEN_ELSE) {
                    childState = i == 0 ? formulaState(0) : formulaState(pol);
                } else if (op instanceof Modality || op == Quantifier.ALL || op == Quantifier.EX
                        || op == Equality.EQV) {
                    childState = formulaState(0);
                } else {
                    // atom boundary: the enclosing formula's polarity holds below
                    childState = frozenState(pol);
                }
                todo.push(t.sub(i));
                todoState.push(childState);
            }
        }
        final OccInfo info = new OccInfo(opsAny, relPlus, relMinus);
        cache.put(cf, info);
        return info;
    }

    /** Whether the operator belongs to the formula layer the polarity walk toggles through. */
    private static boolean isConnective(Operator op) {
        return op == Junctor.NOT || op == Junctor.AND || op == Junctor.OR || op == Junctor.IMP
                || op == Junctor.TRUE || op == Junctor.FALSE || op == IfThenElse.IF_THEN_ELSE;
    }

    /**
     * Counts the given compound candidates over the sequent's formulas. Each formula is walked once
     * over its distinct subterms; a subterm matches a candidate up to term labels. A candidate
     * reaching {@link #CAP} formulas is done and leaves the walk, and the walk ends when no
     * candidate
     * is left.
     */
    private static void countCompounds(Sequent seq, List<Term> unknown,
            Map<Term, Integer> results) {
        final List<Term> active = new ArrayList<>(unknown);
        final ArrayDeque<Term> todo = new ArrayDeque<>();
        final Set<Term> visited = new HashSet<>();
        // Insertion-ordered: the counts below are merged in hit order.
        final Set<Term> hits = new LinkedHashSet<>();
        for (final SequentFormula cf : seq) {
            if (active.isEmpty()) {
                break;
            }
            visited.clear();
            hits.clear();
            todo.push(cf.formula());
            while (!todo.isEmpty() && hits.size() < active.size()) {
                final Term t = todo.pop();
                if (!visited.add(t)) {
                    continue;
                }
                for (final Term c : active) {
                    // Terms equal up to labels share the cached name hash, so the hash compare
                    // rejects almost every pair before the structural comparison.
                    if (t.nameHash() == c.nameHash() && !hits.contains(c)
                            && ((JTerm) t).equalsModProperty(c, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                        hits.add(c);
                    }
                }
                for (int i = 0; i < t.arity(); i++) {
                    todo.push(t.sub(i));
                }
            }
            todo.clear();
            for (final Term c : hits) {
                final int n = results.merge(c, 1, Integer::sum);
                if (n >= CAP) {
                    active.remove(c);
                }
            }
        }
    }
}
