// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

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