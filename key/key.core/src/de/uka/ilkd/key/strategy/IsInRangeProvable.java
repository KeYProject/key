package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.PredictCostProver;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class IsInRangeProvable implements Feature {

    public IsInRangeProvable() {
        
    }
    
    
    private ImmutableSet<Term> collectEquationsAndInEquations(Sequent seq, Services services) {
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        final HashSet<Operator> ops = new HashSet<>();
        ops.add(services.getTypeConverter().getIntegerLDT().getLessOrEquals());
        ops.add(services.getTypeConverter().getIntegerLDT().getLessThan());
        ops.add(services.getTypeConverter().getIntegerLDT().getGreaterThan());
        ops.add(services.getTypeConverter().getIntegerLDT().getGreaterOrEquals());
        for (SequentFormula sf : seq.antecedent()) {
            final Operator op = sf.formula().op();
            if (op == Equality.EQUALS || ops.contains(op)) {
                result.add(sf.formula());
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            final Operator op = sf.formula().op();
            if (op == Equality.EQUALS || ops.contains(op)) {
                result = result.add(services.getTermBuilder().not(sf.formula()));
            }
        }        
        
        return result;
    }
    
    
    @Override
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        TacletApp tapp = (TacletApp) app;
        
        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();
        final ImmutableSet<Term> axioms = collectEquationsAndInEquations(goal.sequent(), services);
                
        final Term termToCheck = pos.subTerm().sub(0);
        Term toProveGEQ = tb.gt(termToCheck,tb.zTerm(Integer.MAX_VALUE));
                
        long geqCost = PredictCostProver.computerInstanceCost(new Substitution(DefaultImmutableMap.<QuantifiableVariable, Term>nilMap()), 
                toProveGEQ, axioms, services);
        if (geqCost == -1) {
            return TopRuleAppCost.INSTANCE;
        }
        Term toProveLEQ = tb.lt(termToCheck,tb.zTerm(Integer.MIN_VALUE));              
        long leqCost = PredictCostProver.computerInstanceCost(new Substitution(DefaultImmutableMap.<QuantifiableVariable, Term>nilMap()), 
                toProveLEQ, axioms, services);
        if (leqCost == -1) {
            return TopRuleAppCost.INSTANCE;
        }
        
        if (leqCost == 0 && geqCost == 0) {
            return NumberRuleAppCost.getZeroCost();
        }
        return TopRuleAppCost.INSTANCE;
    }

}
