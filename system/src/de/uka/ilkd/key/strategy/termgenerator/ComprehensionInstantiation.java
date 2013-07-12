package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;

public class ComprehensionInstantiation implements TermGenerator {

    public static final TermGenerator INSTANCE = new ComprehensionInstantiation();
    
    private Sequent last = Sequent.EMPTY_SEQUENT;
    private Set<Term> lastCandidates = new HashSet<Term>(); 
    
    
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        
        final Sequent seq = goal.sequent();
        final Set<Term> terms;
        if (seq != last) {
            terms = new HashSet<Term>();
            for (SequentFormula sf : seq) {
                enumerateTerms(sf.formula(), terms);
            }
            last = seq;
            lastCandidates = Collections.unmodifiableSet(terms);
        } else {
            terms = lastCandidates;
        }

        final Term comprehension = pos.subTerm();

        final Metavariable mv = new Metavariable(new Name("$MV$"), comprehension.boundVars().last().sort());

        final Term trigger = TermBuilder.DF.tf().createTerm(comprehension.op(), 
                new ImmutableArray<Term>(comprehension.sub(0), TermBuilder.DF.var(mv), 
                comprehension.sub(2)), comprehension.boundVars(), comprehension.javaBlock());

        final Set<Term> instances = computeInstances(goal, comprehension, mv, trigger, terms);
                
        return instances.iterator();
    }


    private HashSet<Term> computeInstances(Goal goal, final Term comprehension,
            final Metavariable mv, final Term trigger, Set<Term> terms) {
        HashSet<Term> instances = new HashSet<Term>();
        for (final Term t : terms) {
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, goal.proof().getServices()); 
            if (c.isSatisfiable()) {
                if (c.getInstantiation(mv) != null && 
                        !c.getInstantiation(mv).equalsModRenaming(comprehension.sub(1))) {
                    instances.add(c.getInstantiation(mv));
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
