/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

class Instantiation {


    /** universally quantifiable variable bound in<code>allTerm</code> */
    private final QuantifiableVariable firstVar;

    private final Term matrix;

    /**
     * Literals occurring in the sequent at hand. This is used for branch prediction
     */
    private ImmutableSet<JTerm> assumedLiterals = DefaultImmutableSet.nil();

    /** HashMap from instance(<code>Term</code>) to cost <code>Long</code> */
    private final Map<Term, Long> instancesWithCosts = new LinkedHashMap<>();
    /**
     * The recorded instances bucketed by {@link Term#nameHash()}. Two terms equal up to term
     * labels share that hash, so the label-insensitive duplicate check in
     * {@link #addInstance(Substitution, long)} compares only within one bucket instead of
     * scanning every recorded instance.
     */
    private final Map<Integer, List<Term>> instancesByNameHash = new HashMap<>();

    /** The tie-break scorer, prepared lazily on the first tie-break request and reused. */
    private QuantifierInstantiationTieBreak.Scorer scorer;

    /** The strategy the {@link #scorer} was prepared with; a change re-prepares it. */
    private QuantifierInstantiationTieBreak scorerStrategy;

    /** the <code>TriggersSet</code> of this <code>allTerm</code> */
    private final TriggersSet triggersSet;

    /** Equality reasoning over the sequent's assumed equalities, shared across cost predictions. */
    private final Congruence congruence;

    /** The sequent, kept for the tie-break view. */
    private final Sequent sequent;

    /** The services, kept for the tie-break view. */
    private final Services services;

    private Instantiation(Term allterm, Sequent seq, Services services, boolean classic) {
        this.sequent = seq;
        this.services = services;
        firstVar = allterm.varsBoundHere(0).get(0);
        matrix = TriggerUtils.discardQuantifiers(allterm);
        /* Terms bound in every formula on <code>goal</code> */
        triggersSet = TriggersSet.create((JTerm) allterm, services, classic);
        assumedLiterals = initAssertLiterals(seq, services);
        congruence = new Congruence(assumedLiterals, services);
        assumedLiterals = normalizeAll(assumedLiterals);
        addInstances(sequentToTerms(seq), services);
        // write-coordinate candidates are part of the theory-aware selection, dropped in classic
        if (!classic) {
            addStoreCoordinateInstances((JTerm) matrix, services);
        }
    }

    /**
     * Heap-aware instance candidates from write coordinates: where the matrix reads an array
     * through a built-up heap, {@code select(... store(h, o, arr(c), v) ..., o, arr(j))} with
     * quantified index {@code j}, the written index {@code c} is a candidate for {@code j}.
     * Instantiating with it lets the select collapse by the select-over-store rules, which is
     * how such a quantified formula speaks about the stored value. Trigger matching cannot
     * produce these candidates: the store coordinate contains no quantified variable, so no
     * trigger binds {@code j} to it. The candidates go through the same cost computation as
     * matched ones, so useless coordinates are excluded or ranked down as usual.
     */
    private void addStoreCoordinateInstances(JTerm term, Services services) {
        final var heapLDT = services.getTypeConverter().getHeapLDT();
        // isSelectOp tests the operator directly. Do not build getSelect(term.sort()): that
        // constructs a select of the subterm's sort, which fails for e.g. the Null sort.
        if (heapLDT.isSelectOp(term.op())) {
            final JTerm field = term.sub(2);
            if (field.op() == heapLDT.getArr() && field.freeVars().contains(firstVar)) {
                collectWrittenIndices(term.sub(0), term.sub(1), services);
            }
        }
        for (int i = 0; i < term.arity(); i++) {
            addStoreCoordinateInstances(term.sub(i), services);
        }
    }

    /** Adds every ground index written on {@code obj}'s array fields in {@code heap}. */
    private void collectWrittenIndices(JTerm heap, JTerm obj, Services services) {
        final var heapLDT = services.getTypeConverter().getHeapLDT();
        if (heap.sort() != heapLDT.targetSort()) {
            return;
        }
        if (heap.op() == heapLDT.getStore()) {
            final JTerm field = heap.sub(2);
            if (heap.sub(1).equals(obj) && field.op() == heapLDT.getArr()
                    && field.freeVars().isEmpty()) {
                final ImmutableMap<QuantifiableVariable, Term> varMap =
                    DefaultImmutableMap.<QuantifiableVariable, Term>nilMap()
                            .put(firstVar, field.sub(0));
                addInstance(new Substitution(varMap), services);
            }
        }
        for (int i = 0; i < heap.arity(); i++) {
            collectWrittenIndices(heap.sub(i), obj, services);
        }
    }

    private record Cached(Proof proof, Term qf, Sequent seq, boolean classic,
            Instantiation result) {
    }

    /**
     * Per-thread single-entry cache for {@link #create}. The parallel prover computes quantifier
     * cost concurrently, so a shared static cache would hand the same {@link Instantiation} (with
     * its
     * mutable {@code instancesWithCosts}) to several workers and race them. ThreadLocal confines
     * the
     * cache -- and thereby each returned Instantiation -- to one worker, and also drops the
     * cross-proof class-level lock.
     */
    private static final ThreadLocal<Cached> lastCreate = new ThreadLocal<>();

    static Instantiation create(Term qf, Sequent seq, Services services, boolean classic) {
        final Proof proof = services.getProof();
        final Cached cached = lastCreate.get();
        if (cached != null && qf == cached.qf() && seq == cached.seq()
                && classic == cached.classic()) {
            return cached.result();
        }
        if (cached != null && proof != cached.proof()) {
            // The memo belongs to another proof. Drop it before computing, so the other
            // proof's sequent stays reachable only while this entry is in use.
            lastCreate.remove();
        }
        final Instantiation result = new Instantiation(qf, seq, services, classic);
        lastCreate.set(new Cached(proof, qf, seq, classic, result));
        return result;
    }

    private static ImmutableSet<Term> sequentToTerms(Sequent seq) {
        ImmutableList<Term> res = ImmutableList.nil();
        for (final SequentFormula cf : seq) {
            res = res.prepend(cf.formula());
        }
        return DefaultImmutableSet.fromImmutableList(res);
    }

    /**
     * For each trigger, match it against the sequent terms and store every resulting instantiation
     * together with its predicted cost in {@code instancesWithCosts}.
     *
     * @param terms the sequent terms the triggers are matched against
     */
    private void addInstances(ImmutableSet<Term> terms, Services services) {
        for (final Trigger t : triggersSet.getAllTriggers()) {
            for (final Substitution sub : t.getSubstitutionsFromTerms(terms, services)) {
                addInstance(sub, services);
            }
        }
    }

    private void addInstance(Substitution sub, Services services) {
        final long cost =
            PredictCostProver.computerInstanceCost(sub, (JTerm) getMatrix(),
                assumedLiterals, congruence, services);
        if (cost != -1) {
            addInstance(sub, cost);
        }
    }

    /**
     * Pre-normalises the assumed literals once through the congruence, so each candidate's cost
     * prediction reuses the result instead of re-normalising them.
     *
     * @param lits the assumed literals
     * @return the normalised literals, or {@code lits} unchanged when the congruence is trivial
     */
    private ImmutableSet<JTerm> normalizeAll(ImmutableSet<JTerm> lits) {
        if (congruence.isTrivial()) {
            return lits;
        }
        ImmutableSet<JTerm> res = DefaultImmutableSet.nil();
        for (final JTerm l : lits) {
            res = res.add(congruence.normalize(l));
        }
        return res;
    }

    /**
     * Records the instance chosen by <code>sub</code> for the quantified variable with its
     * predicted cost, keeping the least cost when the instance is recorded already.
     *
     * The same instance can be found through different triggers whose matches differ only in term
     * labels: one match picks the term up with an origin label, another without. Term equality is
     * label sensitive, so both variants would enter the table as separate candidates, and the
     * labels would decide which of the two is enumerated first. The table keeps one entry per
     * instance up to term labels: a later variant merges into the entry of the first one found.
     *
     * @param sub the substitution providing the instance
     * @param cost the predicted cost of the instance
     */
    private void addInstance(Substitution sub, long cost) {
        final Term inst =
            sub.getSubstitutedTerm(firstVar);
        Term key = inst;
        Long oldCost = instancesWithCosts.get(inst);
        if (oldCost == null) {
            final List<Term> bucket = instancesByNameHash.get(inst.nameHash());
            if (bucket != null) {
                for (final Term existing : bucket) {
                    if (((JTerm) existing).equalsModProperty(inst,
                        IRRELEVANT_TERM_LABELS_PROPERTY)) {
                        key = existing;
                        oldCost = instancesWithCosts.get(existing);
                        break;
                    }
                }
            }
            if (oldCost == null) {
                instancesByNameHash.computeIfAbsent(inst.nameHash(), h -> new ArrayList<>(2))
                        .add(inst);
            }
        }
        if (oldCost == null || oldCost >= cost) {
            instancesWithCosts.put(key, cost);
        }
    }

    /**
     * @param seq
     * @param services TODO
     * @return all literals in antesequent, and all negation of literal in succedent
     */
    private ImmutableSet<JTerm> initAssertLiterals(Sequent seq,
            TermServices services) {
        ImmutableList<JTerm> assertLits = ImmutableList.nil();
        for (final SequentFormula cf : seq.antecedent()) {
            final Term atom = cf.formula();
            final var op = atom.op();
            if (!(op == Quantifier.ALL || op == Quantifier.EX)) {
                assertLits = assertLits.prepend((JTerm) atom);
            }
        }
        for (final SequentFormula cf : seq.succedent()) {
            final Term atom = cf.formula();
            final var op = atom.op();
            if (!(op == Quantifier.ALL || op == Quantifier.EX)) {
                assertLits = assertLits
                        .prepend(services.getTermBuilder().not((JTerm) atom));
            }
        }
        return DefaultImmutableSet.fromImmutableList(assertLits);
    }

    /**
     * Try to find the cost of an instance(inst) according its quantified formula and current goal.
     */
    static RuleAppCost computeCost(Term inst, Term form, Sequent seq, Services services,
            boolean classic) {
        return create(form, seq, services, classic).computeCostHelp(inst);
    }

    private RuleAppCost computeCostHelp(Term inst) {
        Long cost = instancesWithCosts.get(inst);
        if (cost == null && (inst.op() instanceof ParametricFunctionInstance pfi
                && pfi.getBase().name().equals(JavaDLTheory.CAST_NAME))) {
            cost = instancesWithCosts.get(inst.sub(0));
        }

        if (cost == null) {
            // if (triggersSet)
            return TopRuleAppCost.INSTANCE;
        }
        if (cost == -1) {
            return TopRuleAppCost.INSTANCE;
        }

        return NumberRuleAppCost.create(cost);
    }

    /**
     * The within-band tie-break cost of an instance, from the given tie-break strategy. Creates (or
     * reuses) the instantiation for the quantified formula, prepares the strategy's per-formula
     * facts once, and scores the instance.
     *
     * @param inst the candidate instance
     * @param form the quantified formula
     * @param seq the sequent
     * @param goal the goal, for the branch history the generation signal needs
     * @param services access to the theory operators
     * @param classic whether the classic trigger selection is active
     * @param strategy the tie-break strategy
     * @return the tie-break cost
     */
    static RuleAppCost computeTieBreak(Term inst, Term form, Sequent seq,
            Goal goal, Services services, boolean classic,
            QuantifierInstantiationTieBreak strategy) {
        return create(form, seq, services, classic).tieBreak(inst, goal, strategy);
    }

    /**
     * The tie-break cost of an instance, delegating to {@code strategy}. The strategy's per-formula
     * facts are prepared once on the first request and reused; a change of strategy re-prepares
     * them.
     */
    private RuleAppCost tieBreak(Term inst, Goal goal,
            QuantifierInstantiationTieBreak strategy) {
        if (scorer == null || scorerStrategy != strategy) {
            scorer = strategy.prepare(new QuantifierInstantiationTieBreak.View(
                instancesWithCosts.keySet(), sequent, goal, services));
            scorerStrategy = strategy;
        }
        return NumberRuleAppCost.create(scorer.tieBreak(inst));
    }

    /** get all instances from instancesCostCache subsCache */
    ImmutableSet<Term> getSubstitution() {
        ImmutableSet<Term> res = DefaultImmutableSet.nil();
        for (final Term inst : instancesWithCosts.keySet()) {
            res = res.add(inst);
        }
        return res;
    }

    private Term getMatrix() {
        return matrix;
    }

}
