package de.uka.ilkd.key.smt.model;

/**
 * Represents a sequence in an SMT model.
 * @author mihai
 *
 */
public class Sequence {
	/**
	 * The name of the sequence.
	 */
	private String name;
	/**
	 * The values contained by the sequence.
	 */
	private String[] content;

	public Sequence(int length, String name) {
		super();		
		this.name = name;
		if(length >=0)
		content = new String[length];
	}
	
	public String getName() {
		return name;
	}	
	
	public void setName(String name) {
		this.name = name;
	}

	public int getLength() {
		return content.length;
	}
	
	public String get(int i){
		return content[i];
	}
	
	public void set(int i, String s){
		content[i] = s;
	}
	
	public String toString(){
		String result = "Seq: "+name+"\n";
		result+= "Length: "+content.length+"\n";
		
		for(int i = 0;content!=null && i< content.length; ++i){
			
			result += "["+i+"] = "+content[i]+"\n";
		}
		return result;
	}	

}
