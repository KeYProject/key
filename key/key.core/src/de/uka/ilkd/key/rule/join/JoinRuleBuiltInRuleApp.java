package de.uka.ilkd.key.rule.join;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.sequentToSETriple;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.join.procedures.JoinWithLatticeAbstraction;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionStateWithProgCnt;

/**
 * Rule application class for join rule applications. Is complete iff
 * the joinPartners field as well as the concrete join rule to be used
 * have been set by the corresponding setter function.
 * 
 * @author Dominic Scheurer
 */
public class JoinRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private Node joinNode = null;
    private ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = null;
    private JoinProcedure concreteRule = null;
    
    private SymbolicExecutionStateWithProgCnt thisSEState = null;
    private ImmutableList<SymbolicExecutionState> joinPartnerStates = null;
    private Term distForm = null;

	public JoinRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    protected JoinRuleBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(rule, pio, ifInsts);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }
    
    @Override
    public boolean complete() {
        // We do not check for the suitability of the distinguishing formula
        // since this has already been dealt with in JoinRuleCompletion.
        return joinPartners != null && concreteRule != null && joinNode != null
                && distinguishablePathConditionsRequirement();
    }
    
    private boolean distinguishablePathConditionsRequirement() {
        final Services services = joinNode.proof().getServices();

        // NOTE: Requiring distinguishable path conditions for the abstraction
        // procedures here is an intermediate construction: JoinRule returns
        // if-then-else terms along with abstraction values when lattice
        // abstraction is applied; furthermore, if-then-else is a fallback
        // for unsupported data types.
        // Future finalization: Remove if-then-else fallbacks (can however
        // affect completeness) and check for each variable in the symbolic
        // states whether the corresponding data types are supported by
        // the concrete lattice.
        if (concreteRule.requiresDistinguishablePathConditions() ||
                concreteRule instanceof JoinWithLatticeAbstraction) {
            ImmutableList<SymbolicExecutionState> allStates = ImmutableSLList.nil();
            allStates = allStates.prepend(joinPartnerStates);
            allStates = allStates.prepend(thisSEState.toSymbolicExecutionState());
            
            for (SymbolicExecutionState state1 : allStates) {
                for (SymbolicExecutionState state2: allStates) {
                    if (state1 != state2) {
                        if (!JoinRuleUtils.pathConditionsAreDistinguishable(
                                state1.second, state2.second, services)) {
                            return false;
                        }
                    }
                }
            }

            return true;
        }
        else {
            return true;
        }
    }
    
    // GETTERS AND SETTERS //

    public ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> getJoinPartners() {
        return joinPartners;
    }
    
    public void setJoinPartners(ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners) {
        this.joinPartners = joinPartners;
        
        joinPartnerStates = ImmutableSLList.nil();
        for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> joinPartner : joinPartners) {
            final Services services = joinPartner.first.proof().getServices();
            
            Triple<Term, Term, Term> partnerSEState =
                  sequentToSETriple(joinPartner.first.node(), joinPartner.second, services);
            
            joinPartnerStates = joinPartnerStates.prepend(
                  new SymbolicExecutionState(partnerSEState.first, partnerSEState.second, joinPartner.first.node()));
         }
    }

    public JoinProcedure getConcreteRule() {
		return concreteRule;
	}

	public void setConcreteRule(JoinProcedure concreteRule) {
		this.concreteRule = concreteRule;
	}

	public Node getJoinNode() {
		return joinNode;
	}

	public void setJoinNode(Node joinNode) {
		this.joinNode = joinNode;
		this.thisSEState = JoinRuleUtils.sequentToSETriple(joinNode, super.pio, joinNode.proof().getServices());
	}
	
	public void setDistinguishingFormula(Term distForm) {
	    // null is OK: In this case, we generate the distinguishing
	    // formula automatically. Otherwise, the term must indeed be
	    // a formula.
	    assert distForm == null || distForm.sort() == Sort.FORMULA;
	    
	    this.distForm  = distForm;
	}
    
    public Term getDistinguishingFormula() {
        return distForm;
    }
	
	public SymbolicExecutionStateWithProgCnt getJoinSEState() {
	    return thisSEState;
	}
	
    public ImmutableList<SymbolicExecutionState> getJoinPartnerStates() {
        return joinPartnerStates;
    }

}
