/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.PredictCostProver;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.*;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public class TriggeredInstantiations implements TermGenerator<Goal> {

    public static TermGenerator<Goal> create(boolean skipConditions) {
        return new TriggeredInstantiations(skipConditions);
    }

    private Sequent last = JavaDLSequentKit.getInstance().getEmptySequent();
    private Set<JTerm> lastCandidates = new HashSet<>();
    private ImmutableSet<JTerm> lastAxioms = DefaultImmutableSet.nil();

    private final boolean checkConditions;

    /**
     *
     * @param checkConditions boolean indicating if conditions should be checked
     */
    public TriggeredInstantiations(boolean checkConditions) {
        this.checkConditions = checkConditions;
    }

    /**
     * Generates all instances
     */
    @Override
    public Iterator<org.key_project.logic.Term> generate(RuleApp app, PosInOccurrence pos,
            Goal goal,
            MutableState mState) {
        if (app instanceof TacletApp tapp) {

            final Services services = goal.proof().getServices();
            final Taclet taclet = tapp.taclet();

            final Set<JTerm> terms;
            final Set<JTerm> axiomSet;
            ImmutableSet<JTerm> axioms = DefaultImmutableSet.nil();


            final Sequent seq = goal.sequent();
            if (seq != last) {
                terms = new HashSet<>();
                axiomSet = new HashSet<>();
                computeAxiomAndCandidateSets(seq, terms, axiomSet, services);
                for (JTerm axiom : axiomSet) {
                    axioms = axioms.add(axiom);
                }

                synchronized (this) {
                    last = seq;
                    lastCandidates = terms;
                    lastAxioms = axioms;
                }
            } else {
                synchronized (this) {
                    terms = lastCandidates;
                    axioms = lastAxioms;
                }
            }

            if (taclet.hasTrigger()) {

                final JTerm comprehension = (JTerm) pos.subTerm();

                if (tapp.uninstantiatedVars().size() <= 1) {
                    SVInstantiations svInst = tapp.instantiations();

                    final var sv = taclet.getTrigger().triggerVar();
                    final Sort svSort;
                    if (sv.sort() instanceof GenericSort) {
                        svSort = svInst.getGenericSortInstantiations().getRealSort(sv, services);
                    } else {
                        svSort = sv.sort();
                    }

                    final Metavariable mv = new Metavariable(new Name("$MV$" + sv.name()), svSort);

                    final JTerm trigger =
                        instantiateTerm((JTerm) taclet.getTrigger().trigger(), services,
                            svInst.replace(sv, services.getTermFactory().createTerm(mv), services));

                    final Set<org.key_project.logic.Term> instances =
                        computeInstances(services, comprehension, mv, trigger, terms, axioms, tapp);

                    return instances.iterator();
                } else {
                    // at the moment instantiations with more than one
                    // missing taclet variable not supported
                    return ImmutableSLList.<org.key_project.logic.Term>nil().iterator();
                }
            } else {
                return ImmutableSLList.<org.key_project.logic.Term>nil().iterator();
            }

        } else {
            throw new IllegalArgumentException("At the moment only taclets are supported.");
        }

    }

    private JTerm instantiateTerm(final JTerm term, final Services services,
            SVInstantiations svInst) {
        final SyntacticalReplaceVisitor syn = new SyntacticalReplaceVisitor(new TermLabelState(),
            svInst, services);
        term.execPostOrder(syn);
        return syn.getTerm();
    }

    private void computeAxiomAndCandidateSets(final Sequent seq, final Set<JTerm> terms,
            final Set<JTerm> axioms, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.antecedent(), true, services);
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.succedent(), false, services);
    }

    private void collectAxiomsAndCandidateTerms(final Set<JTerm> terms, final Set<JTerm> axioms,
            final IntegerLDT integerLDT, Semisequent antecedent, boolean inAntecedent,
            TermServices services) {

        for (SequentFormula sf : antecedent) {
            JTerm formula = (JTerm) sf.formula();
            collectTerms(formula, terms, integerLDT);
            if (formula.op() instanceof Function
                    || formula.op() == Equality.EQUALS) {
                axioms.add(
                    inAntecedent ? formula : services.getTermBuilder().not(formula));
            }
        }
    }

    private boolean isAvoidConditionProvable(JTerm cond, ImmutableSet<JTerm> axioms,
            Services services) {

        long cost = PredictCostProver.computerInstanceCost(
            new Substitution(DefaultImmutableMap.nilMap()), cond,
            axioms, services);


        return cost == -1;
    }

    private HashSet<org.key_project.logic.Term> computeInstances(Services services,
            final JTerm comprehension,
            final Metavariable mv, final JTerm trigger, Set<JTerm> terms,
            ImmutableSet<JTerm> axioms,
            TacletApp app) {

        final HashSet<org.key_project.logic.Term> instances = new HashSet<>();
        final HashSet<JTerm> alreadyChecked = new HashSet<>();

        for (final JTerm t : terms) {
            boolean addToInstances = true;
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, services);
            if (c.isSatisfiable()) {
                final JTerm middle = c.getInstantiation(mv, services);
                if (middle != null && !alreadyChecked.contains(middle)) {
                    alreadyChecked.add(middle);
                    if (!checkConditions && app.taclet().getTrigger().hasAvoidConditions()) {
                        ImmutableList<JTerm> conditions =
                            instantiateConditions(services, app, middle);
                        for (JTerm condition : conditions) {
                            if (isAvoidConditionProvable(condition, axioms, services)) {
                                addToInstances = false;
                                break;
                            }
                        }
                    }
                    if (addToInstances) {
                        instances.add(middle);
                    }
                }
            }
        }
        return instances;
    }

    private ImmutableList<JTerm> instantiateConditions(Services services, TacletApp app,
            final JTerm middle) {
        ImmutableList<JTerm> conditions;
        conditions = ImmutableSLList.nil();
        for (var singleAvoidCond : app.taclet().getTrigger().avoidConditions()) {
            conditions =
                conditions.append(
                    instantiateTerm((JTerm) singleAvoidCond, services, app.instantiations()
                            .replace(app.taclet().getTrigger().triggerVar(), middle, services)));
        }
        return conditions;
    }

    private void collectTerms(JTerm instanceCandidate, Set<JTerm> terms, IntegerLDT intLDT) {
        if (instanceCandidate.freeVars().isEmpty()
                && !instanceCandidate.containsJavaBlockRecursive()) {
            terms.add(instanceCandidate);
        }
        if (intLDT.getNumberSymbol() != instanceCandidate.op()) {
            for (int i = 0; i < instanceCandidate.arity(); i++) {
                collectTerms(instanceCandidate.sub(i), terms, intLDT);
            }
        }
    }

}
