package de.uka.ilkd.key.strategy.termgenerator;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
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
import de.uka.ilkd.key.strategy.quantifierHeuristics.HandleArith;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;

public class TriggeredInstantiations implements TermGenerator {

    public static final TermGenerator INSTANCE = new TriggeredInstantiations();

    private Sequent last = Sequent.EMPTY_SEQUENT;
    private Set<Term> lastCandidates = new HashSet<Term>();
    private Set<Term> lastAxioms = new HashSet<Term>();

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
            final Set<Term> axioms;

            final Sequent seq = goal.sequent();
            if (seq != last) {
                terms = new HashSet<Term>();
                axioms = new HashSet<Term>();

                computeAxiomAndCandidateSets(seq, terms, axioms, services);
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
                            taclet.getTriggerTerm(), services,
                            svInst.replace(sv, TermBuilder.DF.var(mv), services));

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
                services, svInst, null);
        term.execPostOrder(syn);
        return syn.getTerm();
    }

    private void computeAxiomAndCandidateSets(final Sequent seq,
            final Set<Term> terms, final Set<Term> axioms, Services services) {
        
        final HashSet<Operator> comps = new HashSet<Operator>();
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        comps.add(integerLDT.getLessOrEquals());
        comps.add(integerLDT.getLessThan());
        comps.add(integerLDT.getGreaterOrEquals());
        comps.add(integerLDT.getGreaterThan());
        comps.add(Equality.EQUALS);
        
        for (SequentFormula sf : seq.antecedent()) {
            collectTerms(sf.formula(), terms, integerLDT);
            if (comps.contains(sf.formula().op())) {
                axioms.add(sf.formula());
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            collectTerms(sf.formula(), terms, integerLDT);
            if (comps.contains(sf.formula().op())) {
                axioms.add(TermBuilder.DF.not(sf.formula()));
            }
        }
    }

    private boolean isAvoidConditionProvable(Term cond, Set<Term> axioms,
            Services services) {

        Term isLEq = HandleArith.provedByArith(cond, services);
        final Iterator<Term> ax = axioms.iterator();
        do {
            if (isLEq.op() == Junctor.TRUE) {
                return true;
            } else if (isLEq.op() == Junctor.FALSE) {
                return false;
            }
            if (ax.hasNext()) {
                final Term axiom = ax.next();
                isLEq = HandleArith.provedByArith(cond, axiom, services);
            } else {
                break;
            }
        } while (true);
        // safe case
        return false;
    }

    private HashSet<Term> computeInstances(Services services,
            final Term comprehension, final Metavariable mv,
            final Term trigger, Set<Term> terms, Set<Term> axioms, TacletApp app) {

        final HashSet<Term> instances = new HashSet<Term>();
        final HashSet<Term> alreadyChecked = new HashSet<Term>();

        for (final Term t : terms) {
            boolean addToInstances = true;
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, services);
            if (c.isSatisfiable()) {
                final Term middle = c.getInstantiation(mv);
                if (middle != null && !alreadyChecked.contains(middle)) {
                    alreadyChecked.add(middle);
                    if (!app.taclet().getTriggerAvoidConditions().isEmpty()) {
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
        for (Term singleAvoidCond : app.taclet().getTriggerAvoidConditions()) {
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
