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