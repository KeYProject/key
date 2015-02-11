package de.uka.ilkd.key.testgen.oracle;

public class OracleLocation {
	
	public static String ALL_FIELDS = "<allFields>";
	
	private String object;
	
	private String field;	
	
	public OracleLocation(String object, String field) {
		this.object = object;
		this.field = field;
	}
	
	public OracleLocation(String object){
		this.object = object;
		this.field = ALL_FIELDS;
	}


	public String getObject() {
		return object;
	}


	public String getField() {
		return field;
	}
	
	public boolean isAllFields(){
		return field.equals(ALL_FIELDS);
	}
	
	public boolean equals(Object o){
		
		if(o instanceof OracleLocation){
			OracleLocation l = (OracleLocation) o;
			return object.equals(l.object) && field.equals(l.field);
		}
		
		return false;
		
	}
	
	public String toString(){
		
		if(field.startsWith("[")){
			return object+field;
		}
		else{
			return object + "."+ field;
		}
		
		
	}
	
}
