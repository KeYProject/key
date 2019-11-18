package de.uka.ilkd.key.testgen.oracle;

public class OracleBinTerm implements OracleTerm{
	
	private String op;
	
	private OracleTerm left;
	
	private OracleTerm right;

	public OracleBinTerm(String op, OracleTerm left,
			OracleTerm right) {
	    super();
	    this.op = op;
	    this.left = left;
	    this.right = right;
    }

	public String getOp() {
		return op;
	}	

	public OracleTerm getLeft() {
		return left;
	}

	public OracleTerm getRight() {
		return right;
	}
	
	public String toString(){
		return "("+left.toString()+" "+op+" "+right.toString()+")";
	}
	
	
	
}
