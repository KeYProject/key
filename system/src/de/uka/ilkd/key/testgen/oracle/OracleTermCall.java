package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

public class OracleTermCall implements OracleTerm {
	
	private OracleMethod method;
	private List<? extends OracleTerm> args;
	
	public OracleTermCall(OracleMethod method, List<? extends OracleTerm> args) {
	    super();
	    this.method = method;
	    this.args = args;
    }
	
	public String toString(){
		String methodName = method.getMethodName();
		String aString = "";
		for(OracleTerm arg  : args){
			aString += " "+arg.toString() + ",";
		}
		if(!args.isEmpty()){
			aString = aString.substring(0, aString.length()-1);
		}
		return methodName+"("+aString+")";		
	}
	
}
