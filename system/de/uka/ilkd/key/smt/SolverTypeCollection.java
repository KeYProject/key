package de.uka.ilkd.key.smt;

import java.util.Iterator;
import java.util.LinkedList;

public class SolverTypeCollection implements Iterable<SolverType>{
    public  final static SolverTypeCollection EMPTY_COLLECTION = new SolverTypeCollection(); 
    
    
    
    private LinkedList<SolverType> types = new LinkedList<SolverType>();
    private String name;
 
    /**
     * 
     * @param type at least on solver type must be passed.
     * @param types
     */
    public SolverTypeCollection(String name, SolverType type, SolverType ... types){
	this.types.add(type);
	this.name = name;
	for(SolverType t : types){
	    this.types.add(t);
	}
    }
    
    public SolverTypeCollection(String [] solverNames){
	
    }
    
    private SolverTypeCollection(){
	
    }
    
    public String name(){
	return name;
    }
    
    public String toString(){
	String s = "";
	Iterator<SolverType> it = types.iterator();
	while(it.hasNext()){
	    SolverType type = it.next();
	    s += type.getName();
	    if(it.hasNext()){
		s+=", ";
	    }	    
	}
	if(s.isEmpty()){
	    return "No solver available.";
	}
	return s;
    }



    @Override
    public Iterator<SolverType> iterator() {
	return types.iterator();
    }
}
