package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * Feature used to check if the value of a given term with <code>moduloXXX</code> 
 * (with <code>XXX</code> being Long, Int, etc.) is in the range of Long, Integer etc.
 */
public class IsInRangeProvable implements Feature {

    public static final IsInRangeProvable INSTANCE = new IsInRangeProvable(250, 5000);    
    
    private final int timeoutInMillis;
    private final int maxRuleApps;
    
    private IsInRangeProvable(int timeoutInMillis, int maxRuleApps) {
        this.timeoutInMillis = timeoutInMillis;
        this.maxRuleApps = maxRuleApps;
    }
    
    /**
     * Helper method used to extract the axioms from a given sequent
     * @param seq the {@link Sequent} from which the axioms are extracted
     * @param ignore the {@link SequentFormula} not to be used as axiom
     * @param services the {@link Services}
     * @return the set of axioms
     */
    private ImmutableSet<Term> collectAxioms(Sequent seq, PosInOccurrence ignore, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        // collect the operators used to identify the formulas of interest in the sequent
        final HashSet<Operator> ops = new HashSet<>();
        ops.add(integerLDT.getLessOrEquals());
        ops.add(integerLDT.getLessThan());
        ops.add(integerLDT.getGreaterThan());
        ops.add(integerLDT.getGreaterOrEquals());
        
        // when extracting we want to ignore the formula on which the rule is applied
        final SequentFormula formulaToIgnore = ignore.sequentFormula();
        
        // extract formulas with equality (on integer terms) or one of the operators in <code>ops</code> as top level operator
        final ImmutableSet<Term> result = 
                extractAssumptionsFrom(seq.antecedent(), false, DefaultImmutableSet.<Term>nil(), ops, formulaToIgnore, services);
        
        return extractAssumptionsFrom(seq.succedent(), true, result, ops, formulaToIgnore, services);
    }

    /**
     * helper method to determine teh formulas in a semisequent to be used as axioms (or their negations)
     * @param semisequent the {@link Semisequent}, i.e., antecedent or succedent from which axioms are extracted
     * @param negated a boolean true if not the formulas of the sequent itself, but their negation should be used as axiom
     * @param assumptions the already identified axioms
     * @param ops the {@link Set} of operators of interest used to identify axiom candidates
     * @param formulaToIgnore the {@link SequentFormula} that should not be used as axiom under any circumstances (the consequence is derived from this formula)
     * @param services the {@link Services}
     * @return the set of axioms (including the already found axioms {@code assumptions}
     */
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


    /**
     * helper methods to filter out the sequent formulas of interest,
     * here those formulas with an equality between ints or any of the operators in
     * ops as top level operator
     * @param ops the {@link Set} of {@link Operator}s 
     * @param integerLDT the {@link IntegerLDT} 
     * @param formula the formula to check
     * @return true if the formula should be used axiom
     */
    private boolean filterSequent(final HashSet<Operator> ops,
            final IntegerLDT integerLDT, final Term formula) {
        return (formula.op() == Equality.EQUALS && 
                formula.sub(0).sort().extendsTrans(integerLDT.targetSort())) || ops.contains(formula.op());
    }
    
    /**
     * checks if the sequent is provable
     * @param seq the {@link Sequent} to be proven
     * @param services the {@link Services}
     * @return true if the sequent could be proven valid
     */
    protected boolean isProvable(Sequent seq, Services services) {
        // prevent chained calls
        if (services.getProof().name().toString().startsWith("IsInRange Proof")) {
            return false;
        }
        
        final ProofStarter ps = new ProofStarter(false);
        final ProofEnvironment env = 
                SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        try {
            ps.init(seq, env, "IsInRange Proof");
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

    /**
     * creates the strategy configuration to be used for the side proof
     * @return the StrategyProperties
     */
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
       
        final ImmutableSet<Term> axioms = collectAxioms(goal.sequent(), pos, services);
                
        Term toProve = createConsequence(pos, services);              
        
        if (isProvable(toSequent(axioms, toProve), services)) {
            return NumberRuleAppCost.getZeroCost();
        }
                    
        return TopRuleAppCost.INSTANCE;
    }


    /**
     * creates the term to be proven to follow from a (possibly empty) set of axioms
     * @param pos the {@link PosInOccurrence} of the focus term
     * @param services the {@link Services}
     * @return the term to prove
     */
    protected Term createConsequence(final PosInOccurrence pos, final Services services) {
        
        final Term termToCheck = pos.subTerm().sub(0);
        final TermBuilder tb = services.getTermBuilder();
        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        
        long upperBound;
        long lowerBound;
        
        if (pos.subTerm().op() == intLDT.getArithModuloLong()) {
            upperBound = Long.MAX_VALUE;
            lowerBound = Long.MIN_VALUE;
        } else if (pos.subTerm().op() == intLDT.getArithModuloInt()) {
            upperBound = Integer.MAX_VALUE;
            lowerBound = Integer.MIN_VALUE;
        } else if (pos.subTerm().op() == intLDT.getArithModuloShort()) {
            upperBound = Short.MAX_VALUE;
            lowerBound = Short.MIN_VALUE;
        } else if (pos.subTerm().op() == intLDT.getArithModuloByte()) {
            upperBound = Byte.MAX_VALUE;
            lowerBound = Byte.MIN_VALUE;
        } else if (pos.subTerm().op() == intLDT.getArithModuloChar()) {
            upperBound = Character.MAX_VALUE;
            lowerBound = Character.MIN_VALUE;
        } else {
            assert false :  "Unknown modulo operation";
            return tb.ff();
        }
        
        final Term toProve = tb.and(tb.geq(termToCheck, tb.zTerm(lowerBound)), 
                tb.leq(termToCheck, tb.zTerm(upperBound)));
        return toProve;
    }


    /**
     * creates the sequent <code>axioms ==> toProve</code>
     * @param axioms set of terms (conjunctive)
     * @param toProve the Term to be proven
     * @return the sequent to be proven valid
     */
    protected Sequent toSequent(ImmutableSet<Term> axioms, Term toProve) {
        Sequent result = Sequent.EMPTY_SEQUENT;        
        for (final Term axiom : axioms) {
            result = result.addFormula(new SequentFormula(axiom), true, true).sequent();
        }        
        return result.addFormula(new SequentFormula(toProve), false, true).sequent();
    }
}
