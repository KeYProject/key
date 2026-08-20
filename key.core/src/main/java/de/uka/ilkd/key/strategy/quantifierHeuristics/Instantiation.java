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
import de.uka.ilkd.key.strategy.quantifierHeuristics.theory.TriggerSupport;
import de.uka.ilkd.key.strategy.quantifierHeuristics.tiebreak.QuantifierInstantiationTieBreak;

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

    /** How much this instantiation is told about the theories. */
    private final TriggerTreatment treatment;

    /** The services, kept for the tie-break view. */
    private final Services services;

    private Instantiation(Term allterm, Sequent seq, Services services,
            TriggerTreatment treatment) {
        this.sequent = seq;
        this.services = services;
        firstVar = allterm.varsBoundHere(0).get(0);
        matrix = TriggerUtils.discardQuantifiers(allterm);
        /* Terms bound in every formula on <code>goal</code> */
        this.treatment = treatment;
        triggersSet = TriggersSet.create((JTerm) allterm, services, treatment.isClassic());
        assumedLiterals = initAssertLiterals(seq, services);
        congruence = new Congruence(assumedLiterals, services);
        assumedLiterals = normalizeAll(assumedLiterals);
        addInstances(sequentToTerms(seq), services);
        addTheoryInstances((JTerm) matrix,
            services.getProfile().getTheorySupports(treatment.isClassic()), services);
    }

    /**
     * Adds the instance candidates the theories supply for {@code term} and descends into its
     * subterms.
     *
     * Matching binds the quantified variable to a subterm of the term it matched, so it never
     * produces an instance that stands in no trigger position. A theory supplies such an instance
     * directly. Which subterms yield one depends on the theory, the descent over the matrix does
     * not, so every support is called on every subterm. A supplied candidate is costed like a
     * matched one.
     *
     * The supports are the ones the trigger treatment selects, so the classic treatment, which
     * has none for the heap, supplies no candidates.
     *
     * @param term a subterm of the matrix
     * @param supports the theories to consult
     * @param services access to the theories
     */
    private void addTheoryInstances(JTerm term, List<? extends TriggerSupport> supports,
            Services services) {
        for (final TriggerSupport support : supports) {
            for (final JTerm inst : support.provideInstances(term, firstVar, services)) {
                final ImmutableMap<QuantifiableVariable, Term> varMap =
                    DefaultImmutableMap.<QuantifiableVariable, Term>nilMap().put(firstVar, inst);
                addInstance(new Substitution(varMap), services, 0);
            }
        }
        for (int i = 0; i < term.arity(); i++) {
            addTheoryInstances(term.sub(i), supports, services);
        }
    }

    private record Cached(Proof proof, Term qf, Sequent seq, TriggerTreatment treatment,
            Instantiation result) {
    }

    /**
     * Per-thread single-entry cache for {@link #create}. The parallel prover computes quantifier
     * cost concurrently, so a shared cache would hand the same {@link Instantiation}, with its
     * mutable {@code instancesWithCosts}, to several workers at once. Confining it to one worker
     * also drops the cross-proof lock the class used to take.
     */
    private static final ThreadLocal<Cached> lastCreate = new ThreadLocal<>();

    static Instantiation create(Term qf, Sequent seq, Services services,
            TriggerTreatment treatment) {
        final Proof proof = services.getProof();
        final Cached cached = lastCreate.get();
        if (cached != null && qf == cached.qf() && seq == cached.seq()
                && treatment == cached.treatment()) {
            return cached.result();
        }
        if (cached != null && proof != cached.proof()) {
            // The memo belongs to another proof. Drop it before computing, so the other
            // proof's sequent stays reachable only while this entry is in use.
            lastCreate.remove();
        }
        final Instantiation result = new Instantiation(qf, seq, services, treatment);
        lastCreate.set(new Cached(proof, qf, seq, treatment, result));
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
        boolean matchedByOwnTerms = false;
        for (final Trigger t : triggersSet.getAllTriggers()) {
            if (t.isTheoryProvided()) {
                continue;
            }
            for (final Substitution sub : t.getSubstitutionsFromTerms(terms, services)) {
                addInstance(sub, services,
                    sub.isSolvedByTheory() ? SOLVED_POSITION_SURCHARGE : 0);
                matchedByOwnTerms = true;
            }
        }
        // Basic matching binds the trigger's metavariable to a term the trigger never read, so
        // the instance speaks about a state the formula does not name. Where none of the formula's
        // own terms match the sequent it is all there is, and costs what it predicts. Where they
        // do match, it is offered behind them, so the search takes it only if nothing cheaper
        // closes the goal. Only the cheapest offer for an instance is recorded.
        for (final Trigger t : triggersSet.getAllTriggers()) {
            if (!t.isTheoryProvided()) {
                continue;
            }
            final ImmutableSet<Substitution> unified =
                t.getSubstitutionsFromTerms(terms, services, false);
            for (final Substitution sub : unified) {
                addInstance(sub, services, 0);
            }
            if (treatment.allowsBasicMatchingOfTheoryTriggers()) {
                final long surcharge = matchedByOwnTerms ? THEORY_TRIGGER_SURCHARGE : 0;
                for (final Substitution sub : t.getSubstitutionsFromTerms(terms, services, true)) {
                    if (!unified.contains(sub)) {
                        addInstance(sub, services, surcharge);
                    }
                }
            }
        }
    }

    /**
     * What an instance costs on top of its prediction when only basic matching of a
     * theory-provided trigger produces it, and the formula's own terms do match the sequent.
     *
     * A predicted cost is a product of clause sizes (see {@link PredictCostProver}), so any
     * surcharge above that range puts such instances behind the supported ones; the exact value
     * does not matter.
     */
    private static final long THEORY_TRIGGER_SURCHARGE = 10000L;

    /**
     * What an instance costs on top of its prediction when a theory solved a disagreeing position
     * to obtain it. The instance is then a term the matched term does not contain, so it is
     * offered behind those the two terms produced by agreeing throughout.
     */
    private static final long SOLVED_POSITION_SURCHARGE = 10000L;


    /**
     * @param sub the instantiation found
     * @param services access to the theories
     * @param surcharge what the instance costs on top of its prediction, zero where one of the
     *        formula's own terms produced it
     */
    private void addInstance(Substitution sub, Services services, long surcharge) {
        long cost =
            PredictCostProver.computerInstanceCost(sub, (JTerm) getMatrix(),
                assumedLiterals, congruence, services);
        if (cost == -1) {
            return;
        }
        addInstance(sub, cost + surcharge);
    }

    /** Normalizes every literal by the congruence, so equal atoms coincide. */
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
            TriggerTreatment treatment) {
        return create(form, seq, services, treatment).computeCostHelp(inst);
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
     * @param treatment how much the heuristic is told about the theories
     * @param strategy the tie-break strategy
     * @return the tie-break cost
     */
    static RuleAppCost computeTieBreak(Term inst, Term form, Sequent seq,
            Goal goal, Services services, TriggerTreatment treatment,
            QuantifierInstantiationTieBreak strategy) {
        return create(form, seq, services, treatment).tieBreak(inst, goal, strategy);
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
