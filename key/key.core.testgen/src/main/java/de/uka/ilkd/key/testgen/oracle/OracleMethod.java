package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

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
		//System.out.println("printing");
		String tab = TestCaseGenerator.TAB;
		String argString = "";

		for(OracleVariable var : args){
			argString += var.getSort().name()+" "+var.getName()+",";
		}	
		if(!args.isEmpty()){
			argString = argString.substring(0, argString.length()-1);		
		}

		String retType = "boolean";
		if(returnType!=null){
			retType = returnType.name().toString();
		}
		return tab + "public "+retType+" "+methodName+ "("+argString+"){\n"
				+tab+ tab+body+"\n"
						+ tab+"}";

	}
}
