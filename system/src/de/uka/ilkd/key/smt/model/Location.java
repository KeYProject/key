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
