package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

public class OracleGenerator {
	
	private Services services;
	
	private static int varNum;
	
	private HashMap<Operator, String> ops;
	
	private OracleConstant constTrue;
	private OracleConstant constFalse;
	
	private Set<OracleMethod> oracleMethods;
	
	private List<OracleVariable> quantifiedVariables;
	
	private List<String> prestateTerms;
	
	private static final String PRE_STRING = "pre_";
	
	public OracleGenerator(Services services,Map<Sort, String> setNames) {
		this.services = services;
		initOps();
		initConsts();
		oracleMethods = new HashSet<OracleMethod>();
		quantifiedVariables = new LinkedList<OracleVariable>();
		prestateTerms = new LinkedList<String>();
	}
	
	private void initConsts(){
		constTrue = new OracleConstant("true",services.getTypeConverter().getBooleanType().getSort());
		constFalse = new OracleConstant("false",services.getTypeConverter().getBooleanType().getSort());		
	}	
	
	private void initOps(){
		ops = new HashMap<Operator,String>();		
		ops.put(Equality.EQV, "==");
		ops.put(Equality.EQUALS, "==");
		ops.put(Junctor.AND, "&&");
		ops.put(Junctor.OR, "!!");
		ops.put(services.getTypeConverter().getIntegerLDT().getLessThan(), "<=");
		ops.put(services.getTypeConverter().getIntegerLDT().getLessThan(), "<");
		ops.put(services.getTypeConverter().getIntegerLDT().getGreaterOrEquals(), ">=");
		ops.put(services.getTypeConverter().getIntegerLDT().getGreaterThan(), ">");
		ops.put(services.getTypeConverter().getIntegerLDT().getAdd(), "+");
		ops.put(services.getTypeConverter().getIntegerLDT().getArithJavaIntAddition(), "+");
		ops.put(services.getTypeConverter().getIntegerLDT().getSub(), "-");
		ops.put(services.getTypeConverter().getIntegerLDT().getJavaSubInt(), "-");
		ops.put(services.getTypeConverter().getIntegerLDT().getMul(), "*");
		ops.put(services.getTypeConverter().getIntegerLDT().getJavaMulInt(), "*");
		ops.put(services.getTypeConverter().getIntegerLDT().getDiv(), "/");
		ops.put(services.getTypeConverter().getIntegerLDT().getJavaDivInt(), "/");
		ops.put(services.getTypeConverter().getIntegerLDT().getMod(), "%");
		ops.put(services.getTypeConverter().getIntegerLDT().getJavaMod(), "%");		
	}	
	
	public OracleTerm generateOracle(Term term){
		Operator op = term.op();
		
		//binary terms
		if(ops.containsKey(op)){			
			OracleTerm left = generateOracle(term.sub(0));
			OracleTerm right = generateOracle(term.sub(1));			
			return new OracleBinTerm(ops.get(op),left,right);			
		}//negation
		else if(op == Junctor.NOT){
			OracleTerm sub = generateOracle(term.sub(0));
			return new OracleNegTerm(sub);
		}
		//true
		else if (op == Junctor.TRUE) {
			return constTrue;
		}
		//false
		else if (op == Junctor.FALSE) {
			return constFalse;
		}
		//quantifiable variable
		else if (op instanceof QuantifiableVariable) {			
			QuantifiableVariable qop = (QuantifiableVariable) op;
			return new OracleVariable(qop.name().toString(), qop.sort());
		}
		//integers
		else if (op == services.getTypeConverter().getIntegerLDT()
		        .getNumberSymbol()) {			
			long num = NumberTranslation.translate(term.sub(0)).longValue();			
			return new OracleConstant(Long.toString(num),term.sort());
		}
		//forall
		else if (op == Quantifier.ALL || op == Quantifier.EX) {
			OracleMethod method = createQuantifierMethod(term);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			return new OracleTermCall(method, args);
		}		
		//if-then-else
		else if(op == IfThenElse.IF_THEN_ELSE){
			OracleMethod method = createIfThenElseMethod(term);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			return new OracleTermCall(method, args);
		}
		//functions
		else if (op instanceof Function) {
			return translateFunction(term);
		}
		
		else{
			throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
		}
		
	}

	private OracleTerm translateFunction(Term term) {
	    Operator op = term.op();
		Function fun = (Function) op;
		String name = fun.name().toString();
	    if(isTrueConstant(op)){
	    	return constTrue;
	    }
	    if(isFalseConstant(op)){
	    	return constFalse;
	    }
	    if(term.subs().size() == 0){
	    	return new OracleConstant(name, term.sort());
	    }
	    if(name.endsWith("select")){
	    	
	    	Term heap = term.sub(0);	    	
	    	OracleTerm heapTerm  = generateOracle(heap);	    	
	    	
	    	Term object = term.sub(1);
	    	OracleTerm objTerm = generateOracle(object);
	    	
	    	Term field = term.sub(2);
	    	OracleTerm fldTerm = generateOracle(field);
	    	String value = objTerm.toString() + "."+fldTerm.toString();
	    	
	    	if(heapTerm.toString().equals("heap")){
	    		if(!objTerm.toString().startsWith(PRE_STRING)){	
	    			prestateTerms.add(objTerm.toString());
	    			return new OracleConstant(PRE_STRING+value, term.sort());
	    		}
	    	}
	    	else{
	    		return new OracleConstant(value, term.sort());
	    	}	    	
	    }	    
	    throw new RuntimeException("Unsupported function found: "+fun.name());
    }
	
	private boolean isTrueConstant(Operator o) {
		return o.equals(services.getTypeConverter().getBooleanLDT().getTrueConst());
	}

	private boolean isFalseConstant(Operator o) {
		return o.equals(services.getTypeConverter().getBooleanLDT().getFalseConst());
	}
	
	public static String generateMethodName(){
		varNum++;
		return "sub"+varNum;
	}
	
	private OracleMethod createIfThenElseMethod(Term term){
			
		String methodName = generateMethodName();
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		
		OracleTerm cond = generateOracle(term.sub(0));
		OracleTerm trueCase = generateOracle(term.sub(1));
		OracleTerm falseCase = generateOracle(term.sub(2));
		
		String body = "if("+cond+"){"
				+ "\n   "+trueCase+""
				+ "\n}else{"
				+ "\n   "+falseCase+""
				+ "\n}";
		
		return new OracleMethod(methodName, args, body, term.sort());		
		
	}
	
	private String getSetName(Sort s){
		
		if(s.equals(Sort.FORMULA)){
			return TestCaseGenerator.ALL_BOOLS;
		}
		else if(s.equals(services.getTypeConverter().getIntegerLDT().targetSort())){
			return TestCaseGenerator.ALL_INTS;
		}
		else if(s.equals(services.getTypeConverter().getLocSetLDT().targetSort())){
			throw new RuntimeException("Not implemented yet.");
			//return TestCaseGenerator.ALL_LOCSETS;
		}
		else if(s.equals(services.getTypeConverter().getHeapLDT().getFieldSort())){
			throw new RuntimeException("Not implemented yet.");
			//return TestCaseGenerator.ALL_FIELDS;
		}
		else if(s.equals(services.getTypeConverter().getHeapLDT().targetSort())){
			throw new RuntimeException("Not implemented yet.");
			//return TestCaseGenerator.ALL_HEAPS;
		}
		else if(s.equals(services.getTypeConverter().getSeqLDT().targetSort())){
			throw new RuntimeException("Not implemented yet.");
			//return TestCaseGenerator.ALL_SEQ:
		}
		
		
		
		return TestCaseGenerator.ALL_OBJECTS;
	}
	
	private OracleMethod createQuantifierMethod(Term term){		
		String methodName = generateMethodName();
		ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		QuantifiableVariable qv = vars.get(0);
		OracleVariable var = new OracleVariable(qv.name().toString(), qv.sort());
				
		String setName = getSetName(qv.sort());
		
		quantifiedVariables.add(var);
		OracleTerm sub = generateOracle(term.sub(0));
		quantifiedVariables.remove(var);
		
		OracleNegTerm neg = new OracleNegTerm(sub);
		
		String body;
		if(term.op() == Quantifier.ALL){
			body = createForallBody(qv, setName, neg);
		}
		else if(term.op() == Quantifier.EX){
			body = createExistsBody(qv, setName, sub);
		}
		else{
			throw new RuntimeException("This is not a quantifier: "+term);
		}		
		
		return new OracleMethod(methodName, quantifiedVariables, body);		
	}

	private String createForallBody(QuantifiableVariable qv, String setName,
            OracleNegTerm neg) {
	    String body = "\nfor("+qv.sort().name()+" : "+setName+"){"
				+ "\n   if("+neg.toString()+"){"
				+ "\n      return false;"
				+ "\n   }"
				+ "\n}"
				+ "\n return true;";
	    return body;
    }
	
	private String createExistsBody(QuantifiableVariable qv, String setName,
            OracleTerm cond) {
	    String body = "\nfor("+qv.sort().name()+" : "+setName+"){"
				+ "\n   if("+cond.toString()+"){"
				+ "\n      return true;"
				+ "\n   }"
				+ "\n}"
				+ "\n return false;";
	    return body;
    }
	
	
	
}