package de.uka.ilkd.key.testgen;

public class Assignment {
	
	private String type;
	private String left;
	private String right;
	public Assignment(String left, String right) {
		super();
		this.type = "";
		this.left = left;
		this.right = right;
	}
	
	
	
	public Assignment(String type, String left, String right) {
		super();
		this.type = type;
		this.left = left;
		this.right = right;
	}



	public String toString(){
		return "\n\t"+type+" "+left+" = "+right+";\n";
	}

}
