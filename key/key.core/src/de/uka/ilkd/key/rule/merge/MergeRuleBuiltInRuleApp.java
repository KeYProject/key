package de.uka.ilkd.key.rule.merge;

import java.util.ArrayList;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithLatticeAbstraction;
import mergerule.MergeRuleUtils;
import mergerule.SymbolicExecutionState;
import mergerule.SymbolicExecutionStateWithProgCnt;

/**
 * Rule application class for join rule applications. Is complete iff
 * the joinPartners field as well as the concrete join rule to be used
 * have been set by the corresponding setter function.
 * 
 * @author Dominic Scheurer
 */
public class MergeRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private Node joinNode = null;
    private ImmutableList<MergePartner> joinPartners = null;
    private MergeProcedure concreteRule = null;
    
    private SymbolicExecutionStateWithProgCnt thisSEState = null;
    private ImmutableList<SymbolicExecutionState> joinPartnerStates = null;
    private Term distForm = null;
    
    private ArrayList<MergeRule.MergeRuleProgressListener> progressListeners = new ArrayList<>();

	public MergeRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    protected MergeRuleBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio,
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
                concreteRule instanceof MergeWithLatticeAbstraction) {
            ImmutableList<SymbolicExecutionState> allStates = ImmutableSLList.nil();
            allStates = allStates.prepend(joinPartnerStates);
            allStates = allStates.prepend(thisSEState.toSymbolicExecutionState());
            
            for (SymbolicExecutionState state1 : allStates) {
                for (SymbolicExecutionState state2: allStates) {
                    if (state1 != state2) {
                        if (!MergeRuleUtils.pathConditionsAreDistinguishable(
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

    public ImmutableList<MergePartner> getJoinPartners() {
        return joinPartners;
    }
    
    public void setJoinPartners(ImmutableList<MergePartner> joinPartners) {
        this.joinPartners = joinPartners;
        joinPartnerStates = MergeRuleUtils.sequentsToSEPairs(joinPartners);
    }

    public MergeProcedure getConcreteRule() {
		return concreteRule;
	}

	public void setConcreteRule(MergeProcedure concreteRule) {
		this.concreteRule = concreteRule;
	}

	public Node getJoinNode() {
		return joinNode;
	}

	public void setJoinNode(Node joinNode) {
		this.joinNode = joinNode;
		this.thisSEState = MergeRuleUtils.sequentToSETriple(joinNode, super.pio, joinNode.proof().getServices());
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
    
    public void registerProgressListener(MergeRule.MergeRuleProgressListener listener) {
        progressListeners.add(listener);
    }

    public void clearProgressListeners() {
        progressListeners = new ArrayList<>();
    }

    public boolean removeProgressListener(MergeRule.MergeRuleProgressListener listener) {
        return progressListeners.remove(listener);
    }
    
    public void fireProgressChange(int progress) {
        progressListeners.forEach(l -> l.signalProgress(progress));
    }

}