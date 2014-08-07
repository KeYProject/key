package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

import de.uka.ilkd.key.logic.sort.Sort;

public class OracleMethod {

	private String methodName;

	private List<OracleVariable> args;

	private String body;
	
	private Sort returnType;

	public OracleMethod(String methodName, List<OracleVariable> args,
			String body) {
		super();
		this.methodName = methodName;
		this.args = args;
		this.body = body;
	}
	
	public OracleMethod(String methodName, List<OracleVariable> args,
			String body, Sort sort) {
		super();
		this.methodName = methodName;
		this.args = args;
		this.body = body;
		this.returnType = sort;
	}

	public String getMethodName() {
		return methodName;
	}

	public List<OracleVariable> getArgs() {
		return args;
	}

	public String getBody() {
		return body;
	}	

	public String toString() {

		String argString = "";

		for(OracleVariable var : args){
			argString += var.getSort().name()+" "+var.getName()+",";
		}		
		argString = argString.substring(0, argString.length()-1);		

		String retType = "boolean";
		if(returnType!=null){
			retType = returnType.name().toString();
		}
		return "public "+retType+" "+methodName+ "("+argString+"){"+body+";}";

	}
}
