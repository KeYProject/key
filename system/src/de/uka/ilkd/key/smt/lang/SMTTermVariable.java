/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTTermVariable extends SMTTerm {
	
	String id;
	SMTSort sort;
	SMTTerm quant;
	
	public SMTTermVariable(String id, SMTSort sort) {
		this.id = Util.processName(id);
		this.sort = sort;
	}
	
	

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public SMTSort getSort() {
		return sort;
	}

	public void setSort(SMTSort sort) {
		this.sort = sort;
	}
	
	/**
	 * @return the quant
	 */
	public SMTTerm getQuant() {
		return quant;
	}

	/**
	 * @param quant the quant to set
	 */
	public void setQuant(SMTTerm quant) {
		this.quant = quant;
	}

	@Override
	public boolean equals (Object term) {
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (!(term instanceof SMTTermVariable))
			return false;
		SMTTermVariable tv = (SMTTermVariable) term;
		
		return this.sort.equals(tv.sort) &&
				this.id.equals(tv.id);
	}

//	public boolean equals (Term term) {
//		if (term == null)
//			return false;
//		
//		if (this == term)
//			return true;
//		
//		if (!(term instanceof TermVariable))
//			return false;
//		TermVariable tv = (TermVariable) term;
//		
//		return this.sort.equals(tv.sort) &&
//		this.id.equals(tv.id);
//	}
//	
//	public boolean equals (TermVariable v) {
//		if (v == null) 
//			return false;
//		
//		if (v == this) 
//			return true;
//		
//		return v.id.equals(id) && v.sort.equals(sort);
//	}
	
	@Override
	public int hashCode() {
		return id.hashCode() + sort.getId().hashCode()*10;
	}
	
	public String toSting (){
		return toString(0);
	}
	public String toString (int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}
		
		return tab + id;
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.add(this);
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return sort;
	}
	
	/** {@inheritDoc} */
	@Override
	public boolean occurs(SMTTermVariable a) {
		// TODO Auto-generated method stub
		return a.id.equals(id);
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(String id) {
		// TODO Auto-generated method stub
		return this.id.equals(id);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
		// TODO Auto-generated method stub
		return this.equals(a) ? b : this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
		// TODO Auto-generated method stub
		return this.equals(a) ? b : this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
		return this;
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		// TODO Auto-generated method stub
		return this.equals(a) ? b : this;
//		return this == a ? b : this;
	}
	
	@Override
	public SMTTermVariable copy () {
		return new SMTTermVariable(this.id, this.sort);
	}

}
