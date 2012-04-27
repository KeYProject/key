package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;

public abstract class AbstractContractRuleApp extends AbstractBuiltInRuleApp {

	protected final Contract instantiation;

	protected AbstractContractRuleApp(BuiltInRule rule, PosInOccurrence pio) {
		this(rule, pio, null);
	}

	protected AbstractContractRuleApp(BuiltInRule rule,
	        PosInOccurrence pio, Contract contract) {
		this(rule, pio, ImmutableSLList.<PosInOccurrence>nil(), contract);
	}
	
	protected AbstractContractRuleApp(BuiltInRule rule,
	        PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
	        Contract contract) {
		super(rule, pio, ifInsts);
		this.instantiation = contract;
	}


    public Contract getInstantiation() {
        return instantiation;
    }
		
    @Override
    public abstract AbstractContractRuleApp tryToInstantiate(Goal goal);

    public abstract AbstractContractRuleApp setContract(Contract contract);

	public boolean complete() {
    	return super.complete() && pio != null && instantiation != null;
    }

    
}
