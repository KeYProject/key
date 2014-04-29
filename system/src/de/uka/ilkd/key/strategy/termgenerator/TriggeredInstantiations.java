// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.termgenerator;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.PredictCostProver;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class TriggeredInstantiations implements TermGenerator {

    public static TermGenerator create(boolean skipConditions) {
        return new TriggeredInstantiations(skipConditions);
    }
    
    private Sequent last = Sequent.EMPTY_SEQUENT;
    private Set<Term> lastCandidates = new HashSet<Term>();
    private ImmutableSet<Term> lastAxioms = DefaultImmutableSet.<Term>nil();
    
    private boolean checkConditions;

    /**
     * 
     * @param checkConditions boolean indicating if conditions should be checked
     */
    public TriggeredInstantiations(boolean checkConditions) {
        this.checkConditions = checkConditions;
    }
    
    @Override
    /**
     * Generates all instances 
     */
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (app instanceof TacletApp) {

            final Services services = goal.proof().getServices();
            final TacletApp tapp = (TacletApp) app;
            final Taclet taclet = tapp.taclet();

            final Set<Term> terms;
            final Set<Term> axiomSet;
            ImmutableSet<Term> axioms = DefaultImmutableSet.<Term>nil();
 
            
            final Sequent seq = goal.sequent();
            if (seq != last) {
                terms = new HashSet<Term>();
                axiomSet = new HashSet<Term>();
                computeAxiomAndCandidateSets(seq, terms, axiomSet, services);
                for (Term axiom : axiomSet) {
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

                final Term comprehension = pos.subTerm();

                if (tapp.uninstantiatedVars().size() <= 1) {
                    SVInstantiations svInst = tapp.instantiations();

                    final SchemaVariable sv = taclet.getTrigger()
                            .getTriggerVar();
                    final Sort svSort;
                    if (sv.sort() instanceof GenericSort) {
                        svSort = svInst.getGenericSortInstantiations()
                                .getRealSort(sv, services);
                    } else {
                        svSort = sv.sort();
                    }

                    final Metavariable mv = new Metavariable(new Name("$MV$"
                            + sv.name()), svSort);

                    final Term trigger = instantiateTerm(
                            taclet.getTrigger().getTerm(), services,
                            svInst.replace(sv, services.getTermBuilder().var(mv), services));

                    final Set<Term> instances = computeInstances(services,
                            comprehension, mv, trigger, terms, axioms, tapp);

                    return instances.iterator();
                } else {
                    // at the moment instantiations with more than one
                    // missing taclet variable not supported
                    return ImmutableSLList.<Term> nil().iterator();
                }
            } else {
                return ImmutableSLList.<Term> nil().iterator();
            }

        } else {
            throw new IllegalArgumentException(
                    "At the moment only taclets are supported.");
        }

    }

    private Term instantiateTerm(final Term term, final Services services,
            SVInstantiations svInst) {
        final SyntacticalReplaceVisitor syn = new SyntacticalReplaceVisitor(
                services, svInst, null, null);
        term.execPostOrder(syn);
        return syn.getTerm();
    }

    private void computeAxiomAndCandidateSets(final Sequent seq,
            final Set<Term> terms, final Set<Term> axioms, Services services) {        
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.antecedent(), true, services);
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.succedent(), false, services);
    }

    private void collectAxiomsAndCandidateTerms(final Set<Term> terms,
            final Set<Term> axioms, final IntegerLDT integerLDT,
            Semisequent antecedent, boolean inAntecedent, TermServices services) {
        
        for (SequentFormula sf : antecedent) {
            collectTerms(sf.formula(), terms, integerLDT);
            if (sf.formula().op() instanceof Function || 
                    sf.formula().op() == Equality.EQUALS) {
                axioms.add(inAntecedent ? sf.formula() : services.getTermBuilder().not(sf.formula()));
            }
        }
    }

    private boolean isAvoidConditionProvable(Term cond, ImmutableSet<Term> axioms,
            Services services) {
        
        long cost = PredictCostProver.computerInstanceCost(
                new Substitution(DefaultImmutableMap.<QuantifiableVariable, Term>nilMap()), 
                cond, axioms, services);
        return cost == -1;
    }

    private HashSet<Term> computeInstances(Services services,
            final Term comprehension, final Metavariable mv,
            final Term trigger, Set<Term> terms, ImmutableSet<Term> axioms, TacletApp app) {

        final HashSet<Term> instances = new HashSet<Term>();
        final HashSet<Term> alreadyChecked = new HashSet<Term>();

        for (final Term t : terms) {
            boolean addToInstances = true;
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, services);
            if (c.isSatisfiable()) {
                final Term middle = c.getInstantiation(mv, services);
                if (middle != null && !alreadyChecked.contains(middle)) {
                    alreadyChecked.add(middle);
                    if (!checkConditions && app.taclet().getTrigger().hasAvoidConditions()) {
                        ImmutableList<Term> conditions = instantiateConditions(services, app, middle);
                        for (Term condition : conditions) {
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

    private ImmutableList<Term> instantiateConditions(Services services,
            TacletApp app, final Term middle) {
        ImmutableList<Term> conditions;
        conditions = ImmutableSLList.<Term> nil();
        for (Term singleAvoidCond : app.taclet().getTrigger().getAvoidConditions()) {
            conditions = conditions.append(instantiateTerm(
                    singleAvoidCond,
                    services,                    
                    app.instantiations().replace(
                            app.taclet().getTrigger().getTriggerVar(), middle,
                            services)));
        }
        return conditions;
    }

    private void collectTerms(Term instanceCandidate, Set<Term> terms,
            IntegerLDT intLDT) {
        if (instanceCandidate.freeVars().isEmpty()
                && !instanceCandidate.isContainsJavaBlockRecursive()) {
            terms.add(instanceCandidate);
        }
        if (intLDT.getNumberSymbol() != instanceCandidate.op()) {
            for (int i = 0; i < instanceCandidate.arity(); i++) {
                collectTerms(instanceCandidate.sub(i), terms, intLDT);
            }
        }
    }

}