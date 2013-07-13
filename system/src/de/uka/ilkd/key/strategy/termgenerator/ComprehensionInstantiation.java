package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.HandleArith;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;

public class ComprehensionInstantiation implements TermGenerator {

    public static final TermGenerator INSTANCE = new ComprehensionInstantiation();
    
    private Sequent last = Sequent.EMPTY_SEQUENT;
    private Set<Term> lastCandidates = new HashSet<Term>(); 
    private Set<Term> lastAxioms = new HashSet<Term>();
    
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Set<Term> terms;
        final Set<Term> axioms;
        final HashSet<Operator> compOps = init(goal);

        final Sequent seq = goal.sequent();
        if (seq != last) {
            terms = new HashSet<Term>();
            axioms = new HashSet<Term>();
            computeAxiomAndCandidateSets(terms, axioms, compOps, seq);
            synchronized(this) {
                last = seq;
                lastCandidates = terms;
                lastAxioms = axioms;
            }
        } else {
            synchronized(this) {
                terms = lastCandidates;
            }
        }

        final Term comprehension = pos.subTerm();

        final Metavariable mv = new Metavariable(new Name("$MV$"), comprehension.boundVars().last().sort());

        final Term trigger = TermBuilder.DF.tf().createTerm(comprehension.op(), 
                new ImmutableArray<Term>(comprehension.sub(0), TermBuilder.DF.var(mv), 
                comprehension.sub(2)), comprehension.boundVars(), comprehension.javaBlock());
        
        final Set<Term> instances = computeInstances(goal, comprehension, mv, trigger, terms);
        
        return instances.iterator();
    }

    private void computeAxiomAndCandidateSets(final Set<Term> terms,
            final Set<Term> axioms, final HashSet<Operator> compOps,
            final Sequent seq) {
        for (SequentFormula sf : seq.antecedent()) {
            enumerateTerms(sf.formula(), terms);
            if (compOps.contains(sf.formula().op())) {
                axioms.add(sf.formula());
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            enumerateTerms(sf.formula(), terms);                
            if (compOps.contains(sf.formula().op())) {
                axioms.add(TermBuilder.DF.not(sf.formula()));
            }
        }
    }

    private HashSet<Operator> init(Goal goal) {
        final Services services = goal.proof().getServices();
        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        final HashSet<Operator> compOps = new HashSet<Operator>();
        compOps.add(intLDT.getLessOrEquals());
        compOps.add(intLDT.getLessThan());
        compOps.add(intLDT.getGreaterOrEquals());
        compOps.add(intLDT.getGreaterThan());
        compOps.add(Equality.EQUALS);
        return compOps;
    }

    private boolean isNotLessOrEqualThan(Term low, Term right, Services services) {
        for (Term axiom : lastAxioms) {
            Term isLEq = HandleArith.provedByArith(TermBuilder.DF.leq(low, right, services), axiom, services);
            if (isLEq.op() == Junctor.TRUE) {
                return false;
            } else if (isLEq.op() == Junctor.FALSE) {
                return true;
            }
        }
        // safe case
        return true;
    }
   
    

    private HashSet<Term> computeInstances(Goal goal, final Term comprehension,
            final Metavariable mv, final Term trigger, Set<Term> terms) {
        HashSet<Term> instances = new HashSet<Term>();
        for (final Term t : terms) {
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, goal.proof().getServices()); 
            if (c.isSatisfiable()) {
                final Term middle = c.getInstantiation(mv);
                if (middle != null && 
                        !middle.equalsModRenaming(comprehension.sub(1))) {                                        
                    final Term low  = comprehension.sub(0);
                    final Term high = comprehension.sub(1);
                    if (isNotLessOrEqualThan(middle, low, goal.proof().getServices())
                            && isNotLessOrEqualThan(high, middle, goal.proof().getServices())) {
                        instances.add(middle);
                    }
                }
            }
        }
        return instances;
    }
    
    
    private void enumerateTerms(Term instanceCandidate, Set<Term> terms) {
        terms.add(instanceCandidate);
        for (int i = 0; i<instanceCandidate.arity(); i++) {
            enumerateTerms(instanceCandidate.sub(i), terms);
        }
    }
    
}
