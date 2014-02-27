/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;



/**
 *
 *
 * @authors Aboubakr Achraf El Ghazi and Fikri Kabakcha
 *
 */
public class SMTSort {
	
	public static final SMTSort BOOL = new SMTSort("Bool");
	public static final SMTSort INT = new SMTSort("Int");
	
	private String id;
	private SMTSort topLevel;
	private SMTFunction is;
	//public List<Sig> superSigs;
	private long bound = -1;
	private long bitSize = -1;
	private SMTFunction boundConst;
	private SMTFunction allocatedAtoms;
	
	public SMTSort(String name){
		this.id = name;
		this.topLevel = this;
		this.is = null;
//		this.superSigs = new LinkedList<Sig>();
	}

	public SMTSort(String name, SMTSort topLevel, SMTFunction is){
		this.id = name;
		this.topLevel = topLevel;
		this.is = is;
//		this.superSigs = new LinkedList<Sig>();
//		this.allocatedAtoms = new Function(id+"_alloc", new LinkedList<Sort>(), Sort.INT);
	}
	
//	public Sort(String name, Sort topLevel, Function is){
//		this.id = name;
//		this.topLevel = topLevel;
//		this.is = is;
//		this.superSigs = superSigs;
//		this.allocatedAtoms = 0;
//	}

	public SMTSort(String name, SMTSort topLevel, SMTFunction is,  int bitSize){
		this.id = name;
		this.topLevel = topLevel;
		this.is = is;
//		this.superSigs = superSigs;
		this.bound = (int) Math.pow(2, bitSize);
		this.bitSize = bitSize;
//		this.bitSize = (int) Math.ceil(Math.log(bitSize) / Math.log(2));
//		this.allocatedAtoms = 0;
	}

	public SMTSort(String name, SMTSort topLevel, SMTFunction is, int bound, SMTFunction allocatedAtoms){
		this.id = name;
		this.topLevel = topLevel;
		this.is = is;
//		this.superSigs = superSigs;
		this.bound = bound;
		this.bitSize = (int) Math.ceil(Math.log(bound) / Math.log(2));
		this.allocatedAtoms = allocatedAtoms;
	}

	public static SMTSort mkBV (long bitSize){
		
		SMTSort sort = new SMTSort ("(_ BitVec " + bitSize+")");
		sort.topLevel = sort;
		sort.is = null;
//		sort.superSigs =  new LinkedList<Sig>();
		sort.bitSize = bitSize;
		sort.bound = (int) Math.pow(2, bitSize);
		
		return sort;
	}
	
	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public SMTSort getTopLevel() {
		return (topLevel != null? topLevel : this);
	}

	public void setTopLevel(SMTSort topLevel) {
		this.topLevel = topLevel;
	}

	public SMTFunction getIs() {
		return is;
	}

	public void setIs(SMTFunction is) {
		this.is = is;
	}

	
//	/**
//	 * @return the superSigs
//	 */
//	public List<Sig> getSuperSigs() {
//		return superSigs;
//	}

//	/**
//	 * @param superSigs the superSigs to set
//	 */
//	public void setSuperSigs(List<Sig> superSigs) {
//		this.superSigs = superSigs;
//	}
	
	/**
	 * @return the bound
	 */
	public long getBound() {
		return bound;
	}

	/**
	 * @param l the bound to set
	 */
	public void setBound(long l) {
		this.bound = l;
		this.bitSize =  (long) Math.ceil(Math.log(l) / Math.log(2));
	}

	/**
	 * @return the bitSize
	 */
	public long getBitSize() {
		return bitSize;
	}

	/**
	 * @param intSize the bitSize to set
	 */
	public void setBitSize(long intSize) {		
		this.bitSize = intSize;
		this.bound = (long) Math.pow(2, intSize);
	}

	/**
	 * @return the boundConst
	 */
	public SMTFunction getBoundConst() {
		return boundConst;
	}

	/**
	 * @param boundConst the boundConst to set
	 */
	public void setBoundConst(SMTFunction boundConst) {
		this.boundConst = boundConst;
	}

	/**
	 * @return the allocatedAtoms
	 */
	public SMTFunction getAllocatedAtoms() {
		return allocatedAtoms;
	}

	/**
	 * @param allocatedAtoms the allocatedAtoms to set
	 */
	public void setAllocatedAtoms(SMTFunction allocatedAtoms) {
		this.allocatedAtoms = allocatedAtoms;
	}

//	/**
//	 * @param sig, sig to add
//	 */
//	public void addSuperSig(Sig sig) {
//		if(!superSigs.contains(sig))
//			superSigs.add(sig);
//	}

//	/**
//	 * @param sigs, sigs to add
//	 */
//	public void addSuperSigs(List<Sig> sigList) {
//		for (Sig sig : sigList) {
//			if(!superSigs.contains(sig))
//				superSigs.add(sig);
//		}
//	}

	public boolean isBV () {
		return bound > 0 && bitSize > 0;
	}
	
	/** Returns true iff ((that is from type sort) and (this.id == that.id)) */
    @Override 
    public boolean equals(Object that) {
    	if (this == that)
    		return true;
    	
        if (!(that instanceof SMTSort)) 
        	return false;
        SMTSort sort = (SMTSort) that;
        
        if (this.isBV() && sort.isBV()) {
        	return this.bitSize == sort.bitSize;
        }
        
        return this.id.equals(sort.id);
    }
    
    @Override
    public int hashCode () {
    	return (int) (id.hashCode() + bitSize *10);
    }
	
	/**
	 * Sort's string value
	 */
	public String toString(){
		if (this.bitSize > 0){
		    return "(define-sort "+id+" () (_ BitVec "+this.bitSize+"))";
		}
		return "(declare-sort "+id+" 0)";
	}

}
