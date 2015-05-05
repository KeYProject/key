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
/**
 * A Location is a pair (objectID, fieldID)
 * @author mihai
 *
 */
public class Location{
	
	private String objectID;
	private String fieldID;
	
	
	
	public Location(String objectID, String fieldID) {
		super();
		this.objectID = objectID;
		this.fieldID = fieldID;
	}
	
	
	public String getObjectID() {
		return objectID;
	}
	public void setObjectID(String objectID) {
		this.objectID = objectID;
	}
	public String getFieldID() {
		return fieldID;
	}
	public void setFieldID(String fieldID) {
		this.fieldID = fieldID;
	}
	
	public String toString(){
		
		return "("+objectID+", "+fieldID+")";
		
		
	}
	
	
	
	
}