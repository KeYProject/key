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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.ProblemTypeInformation;
import de.uka.ilkd.key.smt.SMTObjTranslator;
import de.uka.ilkd.key.smt.lang.SMTSort;
/**
 * Represents an SMT model.
 * @author mihai
 *
 */
public class Model {
	
	private boolean empty;
	/**
	 * Maps constant names to constant values. (constantName, constantValue)
	 */
	private Map<String,String> constants;
	/**
	 * Maps constant values to constant names. (constantValue, constantName1/constantName2/...)
	 */
	private Map<String,String> reversedConstants;
	/**
	 * List of heaps.
	 */
	private List<Heap> heaps;
	/**
	 * List of location sets.
	 */
	private List<LocationSet> locsets;
	/**
	 * List of sequences.
	 */
	private List<Sequence> sequences;
	/**
	 * Type information from the SMT specification.
	 */
	private ProblemTypeInformation types;


	public Model() {
		empty = true;
		constants = new HashMap<String,String>();
		heaps = new LinkedList<Heap>();
		locsets = new LinkedList<LocationSet>();
		reversedConstants = new HashMap<String, String>();
		sequences = new LinkedList<Sequence>();
	}
	
	
	
	

	public boolean isEmpty() {
		return empty;
	}





	public void setEmpty(boolean empty) {
		this.empty = empty;
	}





	/**
	 * Transforms an Object id from binary form to #on, where n is a decimal number.
	 * @param objectID object id in binary form
	 * @return #on, where n is a decimal number.
	 */
	private String processObjectID(String objectID){
		objectID = objectID.replace("#", "");
		objectID = objectID.replace("b", "");
		int i = Integer.parseInt(objectID, 2);
		return "#o"+i;
	}
	/**
	 * Transforms a sequence id from binary form to #sn, where n is a decimal number.
	 * @param sequenceID sequence id in binary form
	 * @return #sn, where n is a decimal number.
	 */
	private String processSeqID(String sequenceID){
		sequenceID = sequenceID.replace("#", "");
		sequenceID = sequenceID.replace("b", "");
		int i = Integer.parseInt(sequenceID, 2);
		return "#s"+i;
	}


	public Map<String, String> getConstants() {
		return constants;
	}
	/**
	 * Rewrites the values of location sets from binary/hexadecimal to a human readable form.
	 */
	private void processLocSetNames(){

		SMTSort locsetSort = this.getTypes().getSort(SMTObjTranslator.LOCSET_SORT);
		SMTSort objectSort = this.getTypes().getSort(SMTObjTranslator.OBJECT_SORT);
		SMTSort fieldSort = this.getTypes().getSort(SMTObjTranslator.FIELD_SORT);
		//for all locsets
		for(LocationSet ls : locsets){
			String name = ls.getName();
			//rewrite the name of the location set
			name = processConstantValue(name, locsetSort);
			ls.setName(name);

			//for all locations
			for(int i = 0; i< ls.size(); ++i){

				Location l = ls.get(i);
				//rewrite object name
				String obj = l.getObjectID();
				obj = processConstantValue(obj, objectSort);				
				l.setObjectID(obj);


				//rewrite field name
				String f = l.getFieldID();
				if(f.startsWith("#b") || f.startsWith("#x")){
					f = processConstantValue(f, fieldSort);				
					String fieldNo = f.replace("#", "").replace("f", "");
					f = "["+fieldNo+"]";
					l.setFieldID(f);
				}


			}		

		}



	}
	/**
	 * Rewrite the object names from binary/hexadecimal to a human readable form.
	 */
	public void processObjectNames(){
		for(Heap h : heaps){
			for(ObjectVal ov : h.getObjects()){
				String newName = processObjectID(ov.getName());
				ov.setName(newName);
			}
		}
	}

	/**
	 * Rewrite the sequence names from binary/hexadecimal to a human readable form.
	 */
	public void processSequenceNames() {
		for(Sequence s : sequences){
			String newName = processSeqID(s.getName());
			s.setName(newName);
		}
	}
	/**
	 * 
	 * @return the heaps
	 */
	public List<Heap> getHeaps() {
		return heaps;
	}
	/**
	 * 
	 * @return the sequences
	 */
	public List<Sequence> getSequences() {
		return sequences;
	}
	/**
	 * 
	 * @return the locsets
	 */
	public List<LocationSet> getLocsets() {
		return locsets;
	}

	/**
	 * @return the types
	 */
	public ProblemTypeInformation getTypes() {
		return types;
	}

	/**
	 * @param types the types to set
	 */
	public void setTypes(ProblemTypeInformation types) {
		this.types = types;
	}
	/**
	 * Fills the reversed constants table.
	 */
	private void fillReversedTable(){
		reversedConstants.clear();
		for(Entry<String,String> e : constants.entrySet()){

			String value = e.getValue();
			String constant = e.getKey();

			if(reversedConstants.containsKey(value)){
				constant = reversedConstants.get(value) + "/"+constant;
			}
			reversedConstants.put(value, constant);	
		}
	}
	/**
	 * Adds a constant to the model.
	 * @param key the constant name
	 * @param value the constant value
	 */
	public void addConstant(String key, String value) {
		constants.put(key, value);
	}
	/**
	 * Adds a heap to the model.
	 * @param e The heap to be added
	 */
	public void addHeap(Heap e) {
		heaps.add(e);
	}
	/**
	 * Adds a location set to the model.
	 * @param e The location set to be added.
	 */
	public void addLocationSet(LocationSet e) {
		locsets.add(e);
	}
	/**
	 * Adds a sequence set to the model.
	 * @param s The sequence to be added.
	 */
	public void addSequence(Sequence s){
		sequences.add(s);
	}
	/**
	 * Transforms a binary value of an any to a human readable form: #sn, where s
	 *  is the first letter of the actual sort name and n is the decimal value of
	 *  corresponding to the any value after the removal of the three type bits 
	 *  and the fill up bits.
	 * @param val original any value
	 * @param s actual sort of the any sort
	 * @return formatted value
	 */
	private String formatAny(String val,SMTSort s){

		val = val.substring(3);
		long bitSize = s.getBitSize();
		val = val.substring(val.length()-(int)bitSize);
		int x = Integer.parseInt(val,2);			
		val = "#"+s.getId().charAt(0)+x;
		val = val.toLowerCase();
		return val;
	}
	/**
	 * Transforms a constant value from binary/hexadecimal form to a human redable form.
	 * @param val binary/hexadecimal value of constant
	 * @param s sort of constant
	 * @return human readable form #sn with s the first letter of the sort of the constant, and n the
	 *  decimal value of the constant 
	 */
	public String processConstantValue(String val,SMTSort s){

		if(val.equals("true") || val.equals("false")){
			return val;
		}

		if(val.startsWith("#x")){
			val = val.replace("#", "");
			val = val.replace("x", "");
			int x = Integer.parseInt(val, 16);
			val = "#b"+Integer.toBinaryString(x);
		}

		val = val.replace("#", "");
		val = val.replace("b", "");

		int x = Integer.parseInt(val,2);

		if(s.getId().equals(SMTObjTranslator.BINT_SORT)){
			long intBound = types.getSort(SMTObjTranslator.BINT_SORT).getBound();
			//long intSize =  types.getSort(SMTObjTranslator.BINT_SORT).getBitSize();


			if(x >= intBound/2){							
				x = (int) (x - intBound);							
			}						
			val = Integer.toString(x);
			return val;
		}

		val = "#"+s.getId().charAt(0)+x;
		val = val.toLowerCase();

		return val;


	}

	/**
	 * Transforms a binary value of an any to a human readable form: #sn, where s
	 *  is the first letter of the actual sort name and n is the decimal value of
	 *  corresponding to the any value after the removal of the three type bits 
	 *  and the fill up bits. 
	 * @param val the original any value in binary/hexadecimal
	 * @return the formatted value
	 */
	public String processAnyValue(String val){

		if(val == null){
			return null;
		}

		//System.out.println("AnyVal: "+val);
		//if val is in hexadecimal transform it to binary first
		if(val.startsWith("#x")){
			val = val.replace("#", "");
			val = val.replace("x", "");
			int x = Integer.parseInt(val, 16);

			long anySize = types.getSort(SMTObjTranslator.ANY_SORT).getBitSize();
			String binString = Integer.toBinaryString(x);

			while(binString.length() < anySize){
				binString = "0" + binString;
			}



			val = "#b"+binString;
		}
		//remove #b prefix of binary string
		val = val.replace("#", "");
		val = val.replace("b", "");			
		
		/*
		 * val now contains the binary string, we check the type bits for all possible sort types
		 */

		//val is of type bint
		if(val.startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.BINT_SORT)))){
			long intBound = types.getSort(SMTObjTranslator.BINT_SORT).getBound();
			long intSize =  types.getSort(SMTObjTranslator.BINT_SORT).getBitSize();
			val = val.substring(3);
			val = val.substring(val.length()-(int)intSize);
			int x = Integer.parseInt(val,2);

			if(x >= intBound/2){							
				x = (int) (x - intBound);							
			}						
			val = Integer.toString(x);						
		}
		//val is of type bool
		else if(val.startsWith(types.getPrefixForSort(SMTSort.BOOL))){
			val = val.substring(3);
			int x = Integer.parseInt(val,2);
			if(x == 0){
				val = "false";
			}
			else{
				val = "true";
			}
		}
		//val is of type sequence
		else if(val.startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.SEQ_SORT)))){
			val = formatAny(val, types.getSort(SMTObjTranslator.SEQ_SORT));
		}
		//val is of type heap - should never happen!
		else if(val.startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.HEAP_SORT)))){
			val = formatAny(val, types.getSort(SMTObjTranslator.HEAP_SORT));
		}	
		//val is of type location set
		else if(val.startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.LOCSET_SORT)))){
			val = formatAny(val, types.getSort(SMTObjTranslator.LOCSET_SORT));
		}
		//val can only be of type object
		else{

			val = val.substring(3);
			long objSize = types.getSort(SMTObjTranslator.OBJECT_SORT).getBitSize();
			val = val.substring(val.length()-(int)objSize);
			int x = Integer.parseInt(val,2);


			val = "#o"+x;
			//			if(reversedConstants.containsKey(val)){
			//				val = val + "/" + reversedConstants.get(val);
			//			}
		}


		return val;



	}


	/**
	 * Transforms the values of array fields of objects from binary/hexidecimal to human readable form.
	 */
	public void processArrayValues(){
		for(Heap h : heaps){
			for(ObjectVal o : h.getObjects()){	

				Sort s = o.getSort();

				if(s==null){
					continue;
				}

				String sortname = s.name().toString();

				if(!sortname.endsWith("[]")){
					continue;
				}

				for(int i = 0; i< o.getLength() ;++i){					
					String val = o.getArrayValue(i);
					val = processAnyValue(val);					
					o.setArrayValue(i, val);
				}

			}
		}
	}
	/**
	 * Transforms values of sequences from binary/hexadecimal to human readable form
	 */
	public void processSeqValues(){

		for(Sequence s : sequences){
			for(int i = 0; i< s.getLength(); ++i){

				String val = s.get(i);

				val = processAnyValue(val);

				s.set(i, val);


			}
		}




	}

	private String getAliasedName(String original){
		return original + "/"+reversedConstants.get(original);
	}
	/**
	 * For all values it adds the names of the constants which have the same values.
	 */
	public void addAliases(){

		for(Heap h : heaps){

			for(ObjectVal o : h.getObjects()){

				if(reversedConstants.containsKey(o.getName())){
					o.setName(getAliasedName(o.getName())); 
				}

				Map<String,String> newFieldValues = new HashMap<String,String>();
				for(Entry<String,String> e : o.getFieldvalues().entrySet()){
					if(reversedConstants.containsKey(e.getValue())){
						newFieldValues.put(e.getKey(), getAliasedName(e.getValue()));
					}
					else{
						newFieldValues.put(e.getKey(), e.getValue());
					}
				}

				o.setFieldvalues(newFieldValues);
				
				if(o.getSort()!=null && o.getSort().name().toString().endsWith("[]")){
					Map<Integer,String> newArrayValues = new HashMap<Integer,String>();
					for (int i = 0; i < o.getLength(); i++) {
						if(reversedConstants.containsKey(o.getArrayValue(i))){
							newArrayValues.put(i, getAliasedName(o.getArrayValue(i)));
						}
						else{
							newArrayValues.put(i, o.getArrayValue(i));
						}
					}	
					o.setArrayValues(newArrayValues);
				}

				Map<String,String> newFunValues = new HashMap<String,String>();
				for(Entry<String,String> e : o.getFunValues().entrySet()){
					if(reversedConstants.containsKey(e.getValue())){
						newFunValues.put(e.getKey(), getAliasedName(e.getValue()));
					}
					else{
						newFunValues.put(e.getKey(), e.getValue());
					}
				}				
				o.setFunValues(newFunValues);




			}

		}
		
		for(LocationSet ls : locsets){
			if(reversedConstants.containsKey(ls.getName())){
				ls.setName(getAliasedName(ls.getName()));
			}
			List<Location> newLocations = new LinkedList<Location>();
			for(Location l : ls.getLocations()){
				String newObjectID = reversedConstants.containsKey(l.getObjectID()) ? getAliasedName(l.getObjectID()) : l.getObjectID();
				String newFieldID = reversedConstants.containsKey(l.getFieldID()) ? getAliasedName(l.getFieldID()) : l.getFieldID();
				newLocations.add(new Location(newObjectID, newFieldID));
				
			}
			ls.setLocations(newLocations);
		}
		
		for(Sequence s : sequences){
			if(reversedConstants.containsKey(s.getName())){
				s.setName(getAliasedName(s.getName()));
			}
			
			for(int i= 0; i<s.getLength();++i){
				
				if(reversedConstants.containsKey(s.get(i))){
					s.set(i, getAliasedName(s.get(i)));
				}
				
				
			}
			
		}
		
		
		

	}
	
	
	
	
	public static String removePipes(String s){
		
		if(s.startsWith("|")){
			s = s.substring(1);			
		}
		
		if(s.endsWith("|")){
			s = s.substring(0, s.length()-1);
		}
		
		return s;
		
		
	}
	
	
	

	/**
	 * Transforms the values of constants and object fields from binary/hexadecimal to a human readable from.
	 */
	public void processConstantsAndFieldValues(){

		//process constants
		Map<String,String> newConstants = new HashMap<String, String>();
		for(String c : constants.keySet()){

			String value = constants.get(c);
			SMTSort s = types.getTypeForConstant(c);
			if(s == null){
				System.err.println("No sort for: "+c);
			}
			else{
				newConstants.put(c, processConstantValue(value,s));
			}



		}

		constants = newConstants;
		fillReversedTable();

		for(Heap h : heaps){

			for(ObjectVal o : h.getObjects()){
				Map<String,String> newFieldValues = new HashMap<String, String>();
				for(String f : o.getFieldvalues().keySet()){

					String value = o.getFieldvalues().get(f);
					newFieldValues.put(f, processAnyValue(value));


				}			
				o.setFieldvalues(newFieldValues);
			}

		}

		processLocSetNames();

	}


	public String toString(){

		String result = "Constants";
		result += "\n-----------\n\n";
		for(Entry<String, String> e : constants.entrySet()){
			result += e.getKey() + " = " + e.getValue();
			result += "\n";
		}

		result += "\n";
		result += "\nHeaps";
		result += "\n-----------";
		for(Heap h : heaps){
			result += "\n";
			result += h.toString();
		}
		result += "\n";
		result+= "\nLocation Sets";
		result += "\n-----------";
		for(LocationSet ls : locsets){
			result += "\n";
			result += ls.toString();
		}
		result += "\n";
		result += "\nSequences";
		result += "\n-----------";
		for(Sequence s : sequences){
			result +="\n"+s;
		}

		return result;




	}









}
