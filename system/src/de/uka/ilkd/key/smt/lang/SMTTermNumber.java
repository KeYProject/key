/** 
 * Created on: Aug 15, 2011
 */
package de.uka.ilkd.key.smt.lang;


/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTTermNumber extends SMTTerm {

	private long intValue;
	private long bitSize;
	private SMTTerm upp;
	private SMTSort sort;
	
	public SMTTermNumber (int n) {
		this.intValue = n;
		this.bitSize = -1;
	}
	
	public SMTTermNumber (long n){
		this.intValue = n;
		this.bitSize = -1;
	}

	public SMTTermNumber (long intValue, long bitSize,SMTSort sort) {
		this.intValue = intValue;
		this.bitSize = bitSize;
		this.sort = sort;
	}

	/**
	 * @return the intValue
	 */
	public long getIntValue() {
		return intValue;
	}
    
	/**
	 * @param intValue the intValue to set
	 */
	public void setIntValue(int intValue) {
		this.intValue = intValue;
	}

	/**
	 * @return the bitSize
	 */
	public long getBitSize() {
		return bitSize;
	}

	/**
	 * @param bitSize the bitSize to set
	 */
	public void setBitSize(int bitSize) {
		this.bitSize = bitSize;
	}

	/**
	 * @return the upp
	 */
	public SMTTerm getUpp() {
		return upp;
	}

	/**
	 * @param upp the upp to set
	 */
	public void setUpp(SMTTerm upp) {
		this.upp = upp;
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		
		if(sort!=null){
			return sort;
		}
		
		if (bitSize > 0)
			return SMTSort.mkBV(bitSize);
		else 
			return SMTSort.INT;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(SMTTermVariable a) {
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(String id) {
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		return this;
	}
	
	@Override
	public SMTTermNumber copy () {
		return new SMTTermNumber(this.intValue, this.bitSize, this.sort);
	}
	
	public String toSting (){
		return toString(0);
	}
	/** {@inheritDoc} */
	public String toString(int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}
		
		if (bitSize > 0)
			return tab + "(_ bv"+String.valueOf(intValue)+" "+ bitSize + ")";
			
		return tab + String.valueOf(intValue);
	}
	
	@Override
	public boolean equals (Object term) {
		
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (! (term instanceof SMTTermNumber))
			return false;
		SMTTermNumber tn = (SMTTermNumber) term;
		
		return this.intValue == tn.intValue && this.bitSize== tn.bitSize;
	}

	public boolean equals (SMTTerm term) {
		
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (! (term instanceof SMTTermNumber))
			return false;
		SMTTermNumber tn = (SMTTermNumber) term;
		
		return this.intValue == tn.intValue && this.bitSize== tn.bitSize;
	}
	
	public boolean equals (SMTTermNumber tn) {
		
		if (this == tn)
			return true;
		
		return this.intValue == tn.intValue && this.bitSize== tn.bitSize;
		
	}
	
	@Override
	public int hashCode() {
		return (int) intValue;
	}

}
