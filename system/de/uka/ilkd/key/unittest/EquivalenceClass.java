package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

import java.util.*;

public class EquivalenceClass{

    private SetOfTerm members;
    private HashMap lb2ex, ub2ex;
    // This flag is used to avoid cycles, when it is checked if a concrete 
    // value for this equivalence class is already determined by a given
    // partial model.
    private boolean visited = false;
    // contains the set of terms whose value is not equal to the value
    // of the terms in this class.
    private SetOfTerm disjointRep = SetAsListOfTerm.EMPTY_SET;
    private Boolean bValue = null;
    private Integer iValue = null;
    private Term trueLit, falseLit;
    private Services serv;
    private static Boolean boolTrue = Model.boolTrue;
    private static Boolean boolFalse = Model.boolFalse;
    private static Term nullTerm = 
    TermFactory.DEFAULT.createFunctionTerm(Op.NULL);


    public EquivalenceClass(SetOfTerm members, Services serv){
	this.members = members;
	lb2ex = new HashMap();
	ub2ex = new HashMap();
	this.serv = serv;
	trueLit = serv.getTypeConverter().
	    convertToLogicElement(BooleanLiteral.TRUE); 
	falseLit = serv.getTypeConverter().
	    convertToLogicElement(BooleanLiteral.FALSE); 
    }

    public EquivalenceClass(Term t1, Term t2, Services serv){
	this(SetAsListOfTerm.EMPTY_SET.add(t1).add(t2), serv);
    }

    public EquivalenceClass(Term t, Services serv){
	this(SetAsListOfTerm.EMPTY_SET.add(t), serv);
    }

    private boolean isInt(Sort s) {
        return s.extendsTrans(serv.getTypeConverter().getIntegerLDT().targetSort());
    }
    
    public boolean isInt(){
	for(IteratorOfTerm it = members.iterator(); it.hasNext(); ){
	    Term t = it.next();
	    return isInt(t.sort());                            
	}
	return false;
    }

    public KeYJavaType getKeYJavaType(){
	IteratorOfTerm it = members.iterator();
	Sort s = it.next().sort();
	while(it.hasNext()){
	    Sort s1=it.next().sort();
	    if(s1.extendsTrans(s)){
		s=s1;
	    }
	}
        KeYJavaType result = serv.getJavaInfo().getKeYJavaType(s); 
        if (result == null && isInt(s)) {
            result = serv.getJavaInfo().
                getKeYJavaType(serv.getTypeConverter().getIntLDT().targetSort());
        }
        return result;
    }

    public boolean isBoolean(){
	for(IteratorOfTerm it = members.iterator(); it.hasNext(); ){
	    if( serv.getTypeConverter().getBooleanLDT().targetSort() == it.next().sort() ){
		return true;
	    }
	}
	return false;
    }
 
    /**
     * Returns the locations that are members of this equivalence class.
     */
    public SetOfTerm getLocations(){
	SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;
	IteratorOfTerm it = members.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    if(ModelGenerator.isLocation(t, serv)){
		locations = locations.add(t);
	    }
	}
	return locations;
    }

    public int hashCode(){
	int result = 0;
	IteratorOfTerm it = members.iterator();
	while(it.hasNext()){
	    result += it.next().toString().hashCode();
	}
	return result;
    }

    public boolean equals(Object o){
	if(!(o instanceof EquivalenceClass)){
	    return false;
	}
	EquivalenceClass eqc = (EquivalenceClass) o;
	if(eqc.members.size() != members.size()){
	    return false;
	}
	IteratorOfTerm it = members.iterator();
	l:while(it.hasNext()){
	    IteratorOfTerm it2 = eqc.members.iterator();
	    Term t = it.next();
	    while(it2.hasNext()){
		if(t.toString().equals(it2.next().toString())){
		    continue l;
		}
	    }
	    return false;
	}
	return true;
    }

    public boolean hasConcreteValue(HashMap term2class){
	if(isInt()) return getConcreteIntValue(term2class) != null;
	if(isBoolean()) return getConcreteBooleanValue(term2class) != null;
	return false;
    }

    /**
     * Assigns a concrete integer value to this equivalence class. Used for
     * model generation.
     */
    public boolean setInteger(int i){
	if(containsLiteral()){
	    return false;
	}
	iValue = new Integer(i);
	return true;
    }

    /**
     * Assigns a concrete boolean value to this equivalence class. Used for
     * model generation.
     */
    public boolean setBoolean(boolean b){
	if(containsLiteral()){
	    return false;
	}
	bValue = bool(b);
	return true;
    }

    public boolean resetValue(){
	if(containsLiteral()){
	    return false;
	}
	bValue = null;
	iValue = null;
	return true;
    }
 
    /**
     * returns true iff a term t=null was found in the antecedent of the
     * underlying sequence for a member t of this class.
     */
    public boolean isNull(){
	return members.contains(nullTerm);
    }

    /**
     * returns true iff a term t=null was found in the succecedent of the
     * underlying sequence for a member t of this class.
     */
    public boolean isNotNull(HashMap term2class){
	IteratorOfTerm it = disjointRep.iterator();
	while(it.hasNext()){
	    Term d = it.next();
	    if(((EquivalenceClass) term2class.get(d)).isNull()){
		return true;
	    }
	}
	return false;
    }

    public SetOfTerm getMembers(){
	return members;
    }

    public void add(Term t){
	members = members.add(t);
    }

    public void add(EquivalenceClass ec){
	members = members.union(ec.getMembers());
    }

    public boolean contains(Term t){
	return members.contains(t); 
    }

    public void addDisjoint(Term t){
	disjointRep = disjointRep.add(t);
    }

    public SetOfTerm getDisjoints(){
	return disjointRep;
    }

    /**
     * Only for classes of sort int.
     * Adds the lower bound <code>bound</code> to the set of lower bounds of
     * this EquivalenceClass. Iff it can be derived from the known bounds 
     * of this class that <code>bound</code> and <code>this</code> denote
     * identical equivalence classes the members of <code>bound</code> are 
     * to this class and true is returned.
     */
    public boolean addLowerBound(EquivalenceClass bound, boolean ex){
	if(bound == this || !isInt()) return false;
	if(ub2ex.containsKey(bound)){
	    if(ex || ((Boolean) ub2ex.get(bound)).booleanValue()){
		throw new ModelGenerationFailureException(
		    "Unsatisfiable bound constraints for "+members);
	    }else{
		lb2ex.remove(bound);
		ub2ex.remove(bound);
		add(bound);
		return true;
	    }
	}
	if(lb2ex.containsKey(bound) && 
	   ((Boolean) lb2ex.get(bound)).booleanValue() ||
	   !lb2ex.containsKey(bound)){
	    lb2ex.put(bound, bool(ex));
	}
	return false;
    }

    private Boolean bool(boolean b){
	return b ?  boolTrue : boolFalse;
    }

    /**
     * Only for classes of sort int.
     * Adds the upper bound <code>bound</code> to the set of upper bounds of
     * this EquivalenceClass. Iff it can be derived from the known bounds 
     * of this class that <code>bound</code> and <code>this</code> denote
     * identical equivalence classes the members of <code>bound</code> are 
     * to this class and true is returned.
     */
    public boolean addUpperBound(EquivalenceClass bound, boolean ex){
	if(bound == this) return false;
	if(lb2ex.containsKey(bound)){
	    if(ex || ((Boolean) lb2ex.get(bound)).booleanValue()){
		throw new ModelGenerationFailureException(
		    "Unsatisfiable bound constraints for "+members);
	    }else{
		lb2ex.remove(bound);
		ub2ex.remove(bound);
		add(bound);
		return true;
	    }
	}
	if(ex || !ub2ex.containsKey(bound)){
	    ub2ex.put(bound, bool(ex));
	}
	return false;
    }

    public int getMinimalConcreteUpperBound(HashMap term2class){
	Iterator it = ub2ex.keySet().iterator();
	int min = Integer.MAX_VALUE;
	while(it.hasNext()){
	    EquivalenceClass ec = (EquivalenceClass) it.next();
	    int current;
	    Integer v = ec.getConcreteIntValue(term2class);
	    if(v == null){
		current = ec.getMinimalConcreteUpperBound(term2class);
	    }else{
		current = v.intValue();
	    }
	    Boolean ex = (Boolean) ub2ex.get(ec);
	    if(ex != null && ex.booleanValue()){
		current--;
	    }
	    if(current<min){
		min = current;
	    }
	}
	return min;
    }

    public int getMaximalConcreteLowerBound(HashMap term2class){
	Iterator it = lb2ex.keySet().iterator();
	int max = Integer.MIN_VALUE;
	while(it.hasNext()){
	    EquivalenceClass ec = (EquivalenceClass) it.next();
	    int current;
	    Integer v = ec.getConcreteIntValue(term2class);
	    if(v == null){
		current = ec.getMaximalConcreteLowerBound(term2class);
	    }else{
		current = v.intValue();
	    }
	    Boolean ex = (Boolean) lb2ex.get(ec);
	    if(ex != null && ex.booleanValue()){
		current++;
	    }
	    if(current>max){
		max = current;
	    }
	}
	return max;
    }

    public boolean consistencyCheck(HashMap term2class){
	if(isInt()){
	    if(getMaximalConcreteLowerBound(term2class) >
	       getMinimalConcreteUpperBound(term2class)){
		return false;
	    }
	    if(getConcreteIntValue(term2class) != null){
		if(getConcreteIntValue(term2class).longValue() > 
		   getMinimalConcreteUpperBound(term2class) ||
		   getConcreteIntValue(term2class).longValue() <
		   getMaximalConcreteLowerBound(term2class)){
		    return false;
		}
		IteratorOfTerm itt = disjointRep.iterator();
		while(itt.hasNext()){
		    EquivalenceClass ec = 
			(EquivalenceClass) term2class.get(itt.next());
		    Integer i = ec.getConcreteIntValue(term2class);
		    if(i != null){
			if(iValue.longValue() == i.longValue()){
			    return false;
			}
		    }
		}	    
	    }
	}else if(isBoolean() && getConcreteBooleanValue(term2class) != null){
	    IteratorOfTerm itt = disjointRep.iterator();
	    while(itt.hasNext()){
		EquivalenceClass ec = 
		    (EquivalenceClass) term2class.get(itt.next());
		Boolean b = ec.getConcreteBooleanValue(term2class);
		if(bValue == b){
		    return false;
		}
	    }
	}
	return true;
    }

    public Boolean getConcreteBooleanValue(HashMap term2class){
	if(!isBoolean()){
	    return null;
	}
	if(containsLiteral() || bValue!=null){
	    return bValue;
	}
	if(visited){
	    return null;
	}else{
	    visited = true;
	}
	IteratorOfTerm it = disjointRep.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    EquivalenceClass ec = (EquivalenceClass) term2class.get(t);
	    Boolean b = ec.getConcreteBooleanValue(term2class);
	    if(b!=null){
		visited = false;
		bValue = bool(!b.booleanValue());
		return bValue;
	    }
	}
	visited = false;
	return null;
    }

    public Integer getConcreteIntValue(HashMap term2class){
	if(!isInt()){
	    return null;
	}
	if(containsLiteral() || iValue!=null){
	    return iValue;
	}
	IteratorOfTerm it = members.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    Operator op = t.op();
	    if(op == serv.getTypeConverter().getIntLDT().getAdd() || 
	       op == serv.getTypeConverter().getLongLDT().getAdd()){
		Integer res = null;
		for(int i=0; i<2; i++){
		    EquivalenceClass ec = 
			(EquivalenceClass) term2class.get(t.sub(i));
		    if(ec != null){
			Integer iv = ec.getConcreteIntValue(term2class);
			if(iv!=null && i==0){
			    res = ec.getConcreteIntValue(term2class);
			}else if(iv!=null){
			    return new Integer(
				iv.intValue() + res.intValue());
			}else{
			    break;
			} 
		    }else{
			try{
			    ProgramElement pe = serv.getTypeConverter().
				convertToProgramElement(t.sub(i));
			    if(pe instanceof IntLiteral){
				if(res == null && i==0){
				    res = new Integer(((IntLiteral) pe).
						      getValue());
				}else if(res != null){
				    return new Integer(
					((IntLiteral) pe).getValue() + 
					res.intValue());		    
				}else{
				    break;
				}
			    }
			}catch(RuntimeException e){
//			    System.out.println(e);
			}			
		    }
		}
		if(res != null){
		    return res;
		}
	    }
	}
	return null;
	//...
    }

    public boolean containsLiteral(){
	IteratorOfTerm it = members.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    if(isBoolean()){
		if(trueLit.equals(t)){
		    if(bValue == null) bValue = boolTrue;
		    return true;
		}else if(falseLit.equals(t)){
		    if(bValue == null) bValue = boolFalse;
		    return true;
		}
	    }
	    if(isInt()){
		try{
		    ProgramElement pe = 
			serv.getTypeConverter().convertToProgramElement(t);
		    boolean negative = false;
		    if(pe instanceof Negative){
			pe = ((Negative) pe).getChildAt(0);
		    }
		    if(pe instanceof IntLiteral){
			if(iValue == null){
			    iValue = new Integer((negative ? "-" : "")+
						 ((IntLiteral) pe).getValue());
			}
			return true;
		    }
		}catch(RuntimeException e){
//		    System.out.println(e);
		}	
	    }
	}
	return false;
    }

    public String toString(){
	return members.toString();
    }
}
