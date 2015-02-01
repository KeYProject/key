// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;


public class SMTTermITE extends SMTTerm {

	SMTTerm condition;

	SMTTerm trueCase;

	SMTTerm falseCase;

	private static final String ITE_STRING = "ite";





	public SMTTermITE(SMTTerm condition, SMTTerm trueCase, SMTTerm falseCase) {
		super();
		this.condition = condition;

		if(condition.sort() != SMTSort.BOOL){
			throw new RuntimeException("ite condition must be bool: "+ condition);
		}	
		this.trueCase = trueCase;
		this.falseCase = falseCase;	
//		if(!trueCase.sort().equals(falseCase.sort())){
//
//			String msg = "true case and false case must have same sorts";
//			msg+= "\ntrue case: "+trueCase.toString();
//			msg+= "\nSort: "+trueCase.sort();
//			msg+= "\nfalse case: "+falseCase.toString();		
//			msg+= "\nSort: "+falseCase.sort();
//			System.err.println("\nWarning:\n"+msg);
//			//throw new RuntimeException(msg);
//		}		
	}

	@Override
	public boolean occurs(SMTTermVariable a) {		
		return condition.occurs(a) || trueCase.occurs(a) || falseCase.occurs(a);		
	}

	@Override
	public boolean occurs(String id) {
		return condition.occurs(id) || trueCase.occurs(id) || falseCase.occurs(id);	
	}

	@Override
	public SMTSort sort() {
		return trueCase.sort();
	}

	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
		return new SMTTermITE(condition.substitute(a, b), trueCase.substitute(a, b), falseCase.substitute(a, b));
	}

	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
		return new SMTTermITE(condition.substitute(a, b), trueCase.substitute(a, b), falseCase.substitute(a, b));
	}

	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
		return new SMTTermITE(condition.replace(a, b), trueCase.replace(a, b), falseCase.replace(a, b));
	}

	@Override
	public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
		return new SMTTermITE(condition.instantiate(a, b), trueCase.instantiate(a, b), falseCase.instantiate(a, b));
	}

	@Override
	public SMTTerm copy() {		
		return new SMTTermITE(condition.copy(), trueCase.copy(), falseCase.copy());
	}

	public String toString(int nestPos) {

		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}

		StringBuffer buff = new StringBuffer();
		buff.append(tab);

		buff.append("("+ITE_STRING);
		buff.append("\n");
		buff.append(condition.toString(nestPos+1));
		buff.append("\n");
		buff.append(trueCase.toString(nestPos+1));
		buff.append("\n");
		buff.append(falseCase.toString(nestPos+1));		
		buff.append("\n" + tab + ")");
		return buff.toString();




	}

	@Override
	public String toString(){
		return toString(0);
	}

	@Override
	public boolean equals(Object that){
		if(this == that){
			return true;
		}
		if(that instanceof SMTTermITE){
			SMTTermITE thatIte = (SMTTermITE) that;
			return thatIte.condition.equals(condition) 
					&& thatIte.trueCase.equals(trueCase) 
					&& thatIte.falseCase.equals(falseCase);			
		}	

		return false;
	}

	/**
	 * @return the condition
	 */
	public SMTTerm getCondition() {
		return condition;
	}

	/**
	 * @return the trueCase
	 */
	public SMTTerm getTrueCase() {
		return trueCase;
	}

	/**
	 * @return the falseCase
	 */
	public SMTTerm getFalseCase() {
		return falseCase;
	}

	/**
	 * @param condition the condition to set
	 */
	public void setCondition(SMTTerm condition) {
		this.condition = condition;
	}

	/**
	 * @param trueCase the trueCase to set
	 */
	public void setTrueCase(SMTTerm trueCase) {
		this.trueCase = trueCase;
	}

	/**
	 * @param falseCase the falseCase to set
	 */
	public void setFalseCase(SMTTerm falseCase) {
		this.falseCase = falseCase;
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.addAll(condition.getQuantVars());
		vars.addAll(trueCase.getQuantVars());
		vars.addAll(falseCase.getQuantVars());
		return vars;
	}
	
	

}