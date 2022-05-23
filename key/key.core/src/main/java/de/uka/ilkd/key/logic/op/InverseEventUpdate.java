package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public final class InverseEventUpdate extends AbstractSortedOperator {

	public final static InverseEventUpdate SINGLETON = new InverseEventUpdate(); 
	   
	 
    private InverseEventUpdate() {
	super(new Name("\\invEvUp"), 
	      new Sort[]{Sort.ANY, Sort.ANY, Sort.ANY}, 
	      Sort.UPDATE,
	      false);
    }
    
    public String toString() {
		return "invEvUp";
	}

}
