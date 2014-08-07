package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public class OracleConstant implements OracleTerm {
	
	private String value;
	
	private Sort sort;
	
	public OracleConstant(String value, Sort sort) {
		this.value = value;
		this.sort = sort;
	}

	public String getValue() {
		return value;
	}
	
	public String toString(){
		return value;
	}
	
	
}
