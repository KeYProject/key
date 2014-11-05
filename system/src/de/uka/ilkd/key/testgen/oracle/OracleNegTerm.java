package de.uka.ilkd.key.testgen.oracle;

public class OracleNegTerm implements OracleTerm{
	
	private OracleTerm sub;	

	public OracleNegTerm(OracleTerm sub) {
		this.sub = sub;
	}
	
	public OracleTerm getSub() {
		return sub;
	}
	
	public String toString(){
		return "!"+sub.toString();
	}
}
