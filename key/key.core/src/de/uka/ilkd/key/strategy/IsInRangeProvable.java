package de.uka.ilkd.key.strategy;

import java.util.HashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.util.ProofStarter;

public class IsInRangeProvable implements Feature {

    public static final IsInRangeProvable INSTANCE = new IsInRangeProvable(250, 5000);    
    
    private final int timeoutInMillis;
    private final int maxRuleApps;
    
    private IsInRangeProvable(int timeoutInMillis, int maxRuleApps) {
        this.timeoutInMillis = timeoutInMillis;
        this.maxRuleApps = maxRuleApps;
    }
    
    
    private ImmutableSet<Term> collectEquationsAndInEquations(Sequent seq, PosInOccurrence ignore, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        // collect the operators used to identify the formulas of interest in the sequent
        final HashSet<Operator> ops = new HashSet<>();
        ops.add(integerLDT.getLessOrEquals());
        ops.add(integerLDT.getLessThan());
        ops.add(integerLDT.getGreaterThan());
        ops.add(integerLDT.getGreaterOrEquals());
        
        // when extracting we want to ignore the formula on which the rule is applied
        final SequentFormula formulaToIgnore = ignore.constrainedFormula();
        
        // extract formulas with equality (on integer terms) or one of the operators in <code>ops</code> as top level operator
        final ImmutableSet<Term> result = 
                extractAssumptionsFrom(seq.antecedent(), false, DefaultImmutableSet.<Term>nil(), ops, formulaToIgnore, services);
        
        return extractAssumptionsFrom(seq.succedent(), true, result, ops, formulaToIgnore, services);
    }


    private ImmutableSet<Term> extractAssumptionsFrom(
            final Semisequent semisequent, boolean negated, ImmutableSet<Term> assumptions,
            final HashSet<Operator> ops, final SequentFormula formulaToIgnore, Services services) {
        
        final TermBuilder tb = services.getTermBuilder();
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        
        for (final SequentFormula sf : semisequent) {
            if (formulaToIgnore != sf) {
                final Term formula = sf.formula();
                if (filterSequent(ops, integerLDT, formula)) {
                    assumptions = assumptions.add(negated ? tb.not(formula) : formula);
                }
            }
        }
        return assumptions;
    }


    private boolean filterSequent(final HashSet<Operator> ops,
            final IntegerLDT integerLDT, final Term formula) {
        return (formula.op() == Equality.EQUALS && 
                formula.sub(0).sort().extendsTrans(integerLDT.targetSort())) || ops.contains(formula.op());
    }
    
    
    protected boolean isProvable(Sequent seq, Services services) {
        final ProofStarter ps = new ProofStarter(false);
        try {
            ps.init(seq, services.getProof().getEnv(), "Strategy Oracle");
        } catch (ProofInputException pie) {
            pie.printStackTrace();
            return false;
        }
        
        final StrategyProperties sp = setupStrategy();
        
        ps.setStrategyProperties(sp);
        ps.setMaxRuleApplications(maxRuleApps);
        ps.setTimeout(timeoutInMillis);  
        final ApplyStrategyInfo info = ps.start();
        
        return info.getProof().closed();
    }


    protected StrategyProperties setupStrategy() {
        final StrategyProperties sp = new StrategyProperties();
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NONE);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_NORMAL);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_OFF);
        return sp;
    }


    @Override
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();
        
        final ImmutableSet<Term> axioms = collectEquationsAndInEquations(goal.sequent(), pos, services);
                
        final Term termToCheck = pos.subTerm().sub(0);
        Term toProve = tb.and(tb.geq(termToCheck, tb.zTerm(Integer.MIN_VALUE)), 
                tb.leq(termToCheck, tb.zTerm(Integer.MAX_VALUE)));              
        
        if (isProvable(toSequent(axioms, toProve), services)) {
            return NumberRuleAppCost.getZeroCost();
        }
                    
        return TopRuleAppCost.INSTANCE;
    }


    private Sequent toSequent(ImmutableSet<Term> axioms, Term toProve) {
        Sequent result = Sequent.EMPTY_SEQUENT;        
        for (final Term axiom : axioms) {
            result = result.addFormula(new SequentFormula(axiom), true, true).sequent();
        }        
        return result.addFormula(new SequentFormula(toProve), false, true).sequent();
    }
}
