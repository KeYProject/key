package de.uka.ilkd.key.strategy.termgenerator;

import java.util.HashSet;
import java.util.Iterator;

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
    
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        
        final Term comprehension = pos.subTerm();
        
        final Metavariable mv = new Metavariable(new Name("$MV$"), comprehension.boundVars().last().sort());

        final Term trigger = TermBuilder.DF.tf().createTerm(comprehension.op(), new ImmutableArray<Term>(comprehension.sub(0), TermBuilder.DF.var(mv), 
                comprehension.sub(2)), comprehension.boundVars(), comprehension.javaBlock());
        
        final Sequent seq = goal.sequent();
        
        final HashSet<Term> terms = new HashSet<Term>();
        for (SequentFormula sf : seq) {
            enumerateTerms(sf.formula(), trigger, terms);
        }
               
        final HashSet<Term> instances = computeInstances(goal, comprehension, mv, trigger, terms);
        
        return instances.iterator();
    }


    private HashSet<Term> computeInstances(Goal goal, final Term comprehension,
            final Metavariable mv, final Term trigger, HashSet<Term> terms) {
        HashSet<Term> instances = new HashSet<Term>();
        for (Term t : terms) {
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
    
    
    private void enumerateTerms(Term instanceCandidate, Term pattern, HashSet<Term> terms) {
        if (instanceCandidate.op() == pattern.op()) {
            terms.add(instanceCandidate);
        }
        for (int i = 0; i<instanceCandidate.arity(); i++) {
            enumerateTerms(instanceCandidate.sub(i), pattern, terms);
        }
    }
    
    

}
