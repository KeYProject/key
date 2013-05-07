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

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;

public class UseDependencyContractApp extends AbstractContractRuleApp {

    private final PosInOccurrence step;
	
	public UseDependencyContractApp(BuiltInRule builtInRule, PosInOccurrence pio) {
	    this(builtInRule, pio, null, null);
    }

	public UseDependencyContractApp(BuiltInRule builtInRule, PosInOccurrence pio,
			Contract instantiation, PosInOccurrence step) {
	    this(builtInRule, pio, ImmutableSLList.<PosInOccurrence>nil(), instantiation, step);
    }
	
    public UseDependencyContractApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
            Contract contract, PosInOccurrence step) {
	    super(rule, pio, ifInsts, contract);
	    this.step = step;

    }

    public UseDependencyContractApp replacePos(PosInOccurrence newPos) {
	    return new UseDependencyContractApp(rule(), newPos, ifInsts, instantiation, step);
    }

    public boolean isSufficientlyComplete() {
    	return pio != null && instantiation != null && !ifInsts.isEmpty();    	
    }
    
    public boolean complete() {
    	return super.complete() && step != null;
    }

	private UseDependencyContractApp computeStep(Sequent seq, Services services) {
		assert this.step == null;
		final List<PosInOccurrence> steps = 
				UseDependencyContractRule.
				 getSteps(this.posInOccurrence(), seq, services);                
		PosInOccurrence l_step = 
				UseDependencyContractRule.findStepInIfInsts(steps, this, services);
		assert l_step != null;/* 
				: "The strategy failed to properly "
				+ "instantiate the base heap!\n"
				+ "at: " + app.posInOccurrence().subTerm() + "\n"
				+ "ifInsts: " + app.ifInsts() + "\n"
				+ "steps: " + steps;*/
		return setStep(l_step);
	}
	
	
	public PosInOccurrence step(Sequent seq, Services services) {
			return step;
	}
	
	public UseDependencyContractApp setStep(PosInOccurrence p_step) {
	    assert this.step == null;
		return new UseDependencyContractApp(rule(), 
	    		posInOccurrence(), ifInsts(), instantiation, p_step);
    }

	@Override
    public UseDependencyContractApp setContract(Contract contract) {
	    return new UseDependencyContractApp(builtInRule, posInOccurrence(), ifInsts, 
	    		contract, step);
    }
	
    public UseDependencyContractRule rule() {
    	return (UseDependencyContractRule) super.rule();
    }

	public UseDependencyContractApp tryToInstantiate(Goal goal) {
    	if (complete()) {
    		return this;
    	}
    	UseDependencyContractApp app = this;

    	final Services services = goal.proof().getServices();

		app = tryToInstantiateContract(services);		
    	
    	if (!app.complete() && app.isSufficientlyComplete()) {
    		app = app.computeStep(goal.sequent(), services);
    	}
    	return app;
    }

	public UseDependencyContractApp tryToInstantiateContract(final Services services) {
	    final Term focus = posInOccurrence().subTerm();
    	final IObserverFunction target = (IObserverFunction) focus.op();
    
    	final Term selfTerm;
    	final KeYJavaType kjt;
    
    	if (target.isStatic()) {
    		selfTerm = null;
    		kjt = target.getContainerType();
    	} else {
    		selfTerm = focus.sub(1);
    		kjt = services.getJavaInfo().getKeYJavaType(
    		        selfTerm.sort());
    	}
    	ImmutableSet<Contract> contracts = UseDependencyContractRule.getApplicableContracts(
    	                services, kjt, target);

    	if (contracts.size() > 0) {
    		return setContract(contracts.iterator().next());
    	}
	    return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
      // TODO
      return null;
    }

    @Override
    public UseDependencyContractApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        //return new UseDependencyContractApp(builtInRule, pio, ifInsts, instantiation, step);
    }


	
}