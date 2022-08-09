package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public class OnlyEventUpdates extends VariableConditionAdapter {

	private final SchemaVariable updateSV;

	public OnlyEventUpdates(SchemaVariable var) {
		this.updateSV = var;
	}

	@Override
	public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
			SVInstantiations instMap, Services services) {
	
		if (var != updateSV) {
			return true;
		}
		
		final Term inst = (Term) instMap.getInstantiation(var);
		
		final Term update = (Term)inst;
		if(update.sort()==Sort.UPDATE) {
			return checkForEvent(update);
		}
		
		return false;
	}

	private boolean checkForEvent(Term update) {
		
		final Operator op = update.op();
		
		if(op instanceof ElementaryUpdate || op == UpdateJunctor.SKIP || op == InverseEventUpdate.SINGLETON|| op == AnonEventUpdate.SINGLETON|| op == InverseAnonEventUpdate.SINGLETON) {
			return false;
		} else if (op==EventUpdate.SINGLETON ) {//|| op instanceof AnonEventUpdate
			return true;
		} else if (op==UpdateJunctor.PARALLEL_UPDATE || op == UpdateJunctor.SEQUENTIAL_UPDATE) {
			return (checkForEvent(update.sub(0)) && checkForEvent(update.sub(1)));
		} else if(op == UpdateApplication.UPDATE_APPLICATION) {
			return checkForEvent(update.sub(1));
		}
		Debug.fail("Forgotten update operator", op.getClass());

		return false;
	}
	
	public String toString() {
		return "\\onlyEventUpdates("+updateSV.name()+")";
	}
	
}
