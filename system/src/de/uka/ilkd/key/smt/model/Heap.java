package de.uka.ilkd.key.smt.model;

import java.util.LinkedList;
import java.util.List;
/**
 * Represents a heap in the SMT model.
 * @author mihai
 *
 */
public class Heap {
	/**
	 * The name of the heap.
	 */
	String name;
	/**
	 * The contained objects.
	 */
	List<ObjectVal> objects;
	/**
	 * Creates a new heap with the given name.
	 * @param name
	 */
	public Heap(String name) {
		this.name= name;
		objects = new LinkedList<ObjectVal>();
	}
	/**
	 * Adds an object to the heap.
	 * @param object
	 * @return
	 */
	public boolean add(ObjectVal object) {
		return objects.add(object);
	}
	
	
	public String toString(){
		String result = "Heap "+name+"\n";
		
		for(ObjectVal o : objects){
			result+= o+"\n";
		}
		
		return result;
		
	}

	/**
	 * @return the objects
	 */
	public List<ObjectVal> getObjects() {
		return objects;
	}
	
	
	/**
	 * 
	 * @return the name
	 */
	public String getName() {
		return name;
	}
	/**
	 * Heaps with equal names are equal.
	 */
	public boolean equals(Object that){
		
		if(that instanceof Heap){
			Heap thatHeap = (Heap) that;
			return thatHeap.name.equals(name);
		}
		
		
		return false;
		
	}
	
	
	
	
	
	
	
	

}
