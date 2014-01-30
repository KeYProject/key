/** 
 * Created on: May 18, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.List;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTTermUnaryOp extends SMTTerm{
	
	public enum Op {
		NOT,
		BVNOT, BVNEG
	};

	private Op operator;
	private SMTTerm sub;
		
	/**
	 * @param operator
	 * @param sub
	 */
	public SMTTermUnaryOp(Op operator, SMTTerm sub) {
		super();
		this.operator = operator;
		this.sub = sub;
		this.sub.upp = this;
	}
	
	
	/**
	 * @return the operator
	 */
	public Op getOperator() {
		return operator;
	}
	/**
	 * @param operator the operator to set
	 */
	public void setOperator(Op operator) {
		this.operator = operator;
	}
	/**
	 * @return the subForm
	 */
	public SMTTerm getSub() {
		return sub;
	}
	/**
	 * @param subForm the subForm to set
	 */
	public void setSub(SMTTerm subForm) {
		this.sub = subForm;
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		return sub.getQuantVars();
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getUQVars() {
		return sub.getUQVars();
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getEQVars() {
		return sub.getEQVars();
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		return sub.getVars();
	}
	
	
	/** {@inheritDoc} */
	@Override
	public boolean occurs (SMTTermVariable a) {
		return sub.occurs(a);
	}

	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return SMTSort.BOOL;
	}
	
	/** {@inheritDoc} */
	@Override
	public boolean occurs (String id) {
		return sub.occurs(id);
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {
//		return new TermUnaryOp(operator, (Term) sub.substitute(a, b));
		return sub.substitute(a, b).unaryOp(operator);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTerm a, SMTTerm b) {
		if (this.equals(a))
			return b;
		
//		return new TermUnaryOp(operator, (Term) sub.substitute(a, b));
		return sub.substitute(a, b).unaryOp(operator);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace (SMTTermCall a, SMTTerm b) {
//		return new TermUnaryOp(operator, (Term) sub.replace(a, b));
		return sub.replace(a, b).unaryOp(operator);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
//		return new TermUnaryOp(operator, (Term) sub.instantiate(a, b));
		return sub.instantiate(a, b).unaryOp(operator);
	}
	
	@Override
	public SMTTermUnaryOp copy () {
		return new SMTTermUnaryOp(this.operator, this.sub.copy());
	}
	
	@Override
	public boolean equals (Object term) {
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (!(term instanceof SMTTermUnaryOp))
			return false;
		SMTTermUnaryOp ut = (SMTTermUnaryOp) term;
		
		return this.operator.equals(ut.operator) &&
				this.sub.equals(ut.sub);
	}

//	public boolean equals (Term term) {
//		if (term == null)
//			return false;
//		
//		if (this == term)
//			return true;
//		
//		if (!(term instanceof TermUnaryOp))
//			return false;
//		TermUnaryOp ut = (TermUnaryOp) term;
//		
//		return this.operator.equals(ut.operator) &&
//		this.sub.equals(ut.sub);
//	}
//
//	public boolean equals (TermUnaryOp ut) {
//		if (ut == null)
//			return false;
//	
//		if (this == ut)
//			return true;
//		
//		return this.operator.equals(ut.operator) &&
//		this.sub.equals(ut.sub);
//	}
	
	@Override
	public int hashCode() {
		return this.operator.hashCode() + this.sub.hashCode()*10;
	}
	
	public String toSting (){
		return toString(0);
	}
	public String toString(int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}
		
		switch (operator) {
		case NOT:
			return tab + "(not" + "\n" + sub.toString(nestPos+1) + "\n" + tab +")";
		case BVNOT:
			return tab + "(bvnot" + "\n" + sub.toString(nestPos+1) + "\n" + tab +")";
		case BVNEG:
			return tab + "(bvneg" + "\n" + sub.toString(nestPos+1) + "\n" + tab +")";
		default:
			throw new RuntimeException("Unexpected: supported unaryOp={NOT}");
		}

	}
	
}
