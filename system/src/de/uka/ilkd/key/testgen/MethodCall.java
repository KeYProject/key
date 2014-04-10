package de.uka.ilkd.key.testgen;

import java.util.List;

public class MethodCall {
	
	String object;
	String methodName;
	List<String> args;
	
	public MethodCall(String object, String methodName, List<String> args) {
		super();
		this.object = object;
		this.methodName = methodName;
		this.args = args;
	}
	
	public String toString(){
		
		String argString = "";
		for(String arg : args){
			argString +=","+arg;
		}
		argString = argString.substring(1);
		
		
		return "\n\t"+object+"."+methodName+"("+argString+");\n";
	}
	
	

}
