package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public class OracleType implements OracleTerm {
	
	private Sort s;

	public OracleType(Sort s) {
		super();
		this.s = s;
	}
	
	public String toString(){
		
		return s.name().toString();
		
	}

}
