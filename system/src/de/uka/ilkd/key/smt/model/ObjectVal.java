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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.sort.Sort;
/**
 * Represents an object inside a heap.
 * @author mihai
 *
 */
public class ObjectVal {
	/**
	 * The name of the object.
	 */
	private String name;
	/**
	 * The length of the object.
	 */
	private int length;
	/**
	 * The sort of the object.
	 */
	private Sort sort;
	/**
	 * True if object is an exact instance of its sort.
	 */
	private boolean exactInstance;
	/**
	 * Maps field names to field values. 
	 */
	private Map<String,String> fieldvalues;
	/**
	 * Maps array fields to array values.
	 */
	private Map<Integer,String> arrayValues;
	/**
	 * Maps function names to function values.
	 * Supported functions are model fields and class invariant.
	 */
	private Map<String,String> funValues;

	public ObjectVal(String name) {
		this.name = name;
		fieldvalues = new HashMap<String,String>();
		arrayValues = new HashMap<Integer,String>();
		funValues = new HashMap<String,String>();
		
	}
	
	public void putFunValue(String fun, String val){		
		funValues.put(fun, val);		
	}

	public void setArrayValue(int i, String val){
		arrayValues.put(i, val);
	}

	public String getArrayValue(int i){
		return arrayValues.get(i);
	}

	/**
	 * @param exactInstance the exactInstance to set
	 */
	public void setExactInstance(boolean exactInstance) {
		this.exactInstance = exactInstance;
	}	

	public boolean isExactInstance() {
		return exactInstance;
	}

	public Map<Integer, String> getArrayValues() {
		return arrayValues;
	}

	public Map<String, String> getFunValues() {
		return funValues;
	}

	public void setName(String name) {
		this.name = name;
	}

	public Sort getSort() {
		return sort;
	}






	public void setSort(Sort sort) {
		this.sort = sort;
	}






	public int getLength() {
		return length;
	}




	public void setLength(int length) {
		this.length = length;
	}




	public String getName() {
		return name;
	}




	/**
	 * @return the fieldvalues
	 */
	public Map<String, String> getFieldvalues() {
		return fieldvalues;
	}



	/**
	 * @param fieldvalues the fieldvalues to set
	 */
	public void setFieldvalues(Map<String, String> fieldvalues) {
		this.fieldvalues = fieldvalues;
	}



	public String get(String field) {
		return fieldvalues.get(field);
	}

	public String put(String field, String value) {
		return fieldvalues.put(field, value);
	}

	public String toString(){




		String tab = "   ";
		
		//for null we don't care about length, type, etc.
		if(name.startsWith("#o0")){
			return tab + "Object "+name+"\n";
		}

		String type = sort==null?"java.lang.Object":sort.name().toString();

		String result = tab + "Object "+name+ "\n";	

		result += tab + tab + "length = "+length + "\n";
		result += tab+tab + "type ="+type+"\n";	
		result += tab+tab + "exactInstance ="+this.exactInstance+"\n";
		//result += tab+tab+"<inv> = "+this.inv+"\n";



		List<String> fields = new LinkedList<String>();
		fields.addAll(fieldvalues.keySet());
		Collections.sort(fields);
		
		for(String field : fields){
			result += tab+tab+field + " = " + fieldvalues.get(field);
			result += "\n"; 
		}
		
		for(String fun : funValues.keySet()){
			result += tab+tab+fun + " = " + funValues.get(fun);
			result += "\n";
		}

		List<Integer> arrfields = new ArrayList<Integer>();
		arrfields.addAll(arrayValues.keySet());
		Collections.sort(arrfields);

		for(int i : arrfields){
			result += tab+tab+"["+i+"] = "+arrayValues.get(i);
			result += "\n";
		}

		return result;		
	}
	/**
	 * Objects with equal names are equal.
	 */
	public boolean equals(Object o){		
		if(o instanceof ObjectVal){			
			ObjectVal ov = (ObjectVal) o;
			return ov.name.equals(name);			
		}		
		return false;		
	}

	public void setArrayValues(Map<Integer, String> newArrayValues) {
		this.arrayValues = newArrayValues;
		
	}

	public void setFunValues(Map<String, String> newFunValues) {
		this.funValues = newFunValues;
		
	}















}