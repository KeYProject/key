package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.PostConstruct;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.NumberTranslation;

public class OracleGenerator {
	
	private Services services;
	
	private static int varNum;
	
	private HashMap<Operator, String> ops;
	
	private OracleConstant constTrue;
	private OracleConstant constFalse;
	
	private Map<Sort, String> setNames;
	
	private Set<OracleMethod> oracleMethods;
	
	public OracleGenerator(Services services,Map<Sort, String> setNames) {
		this.services = services;
		initOps();
		initConsts();
		this.setNames  = setNames;	
		oracleMethods = new HashSet<OracleMethod>();
	}
	
	private void initConsts(){
		constTrue = new OracleConstant("true",services.getTypeConverter().getBooleanType().getSort());
		constFalse = new OracleConstant("false",services.getTypeConverter().getBooleanType().getSort());
		
	}
	
	
	private void initOps(){
		ops = new HashMap<Operator,String>();		
		ops.put(Equality.EQV, "==");
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
	
	
	
	public OracleTerm generateOracle(Term postCondition){
		Operator op = postCondition.op();
		
		//binary terms
		if(ops.containsKey(op)){			
			OracleTerm left = generateOracle(postCondition.sub(0));
			OracleTerm right = generateOracle(postCondition.sub(1));			
			return new OracleBinTerm(ops.get(op),left,right);			
		}//negation
		else if(op == Junctor.NOT){
			OracleTerm sub = generateOracle(postCondition.sub(0));
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
			long num = NumberTranslation.translate(postCondition.sub(0)).longValue();			
			return new OracleConstant(Long.toString(num),postCondition.sort());
		}
		//forall
		else if (op == Quantifier.ALL || op == Quantifier.EX) {
			OracleMethod method = createQuantifierMethod(postCondition);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			return new OracleTermCall(method, args);
		}		
		//if-then-else
		else if(op == IfThenElse.IF_THEN_ELSE){
			OracleMethod method = createIfThenElseMethod(postCondition);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			return new OracleTermCall(method, args);
		}
		//functions
		
		else{
			throw new RuntimeException("Could not translate oracle for: "+postCondition+" of type "+postCondition.op());
		}
		
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
	
	private OracleMethod createQuantifierMethod(Term term){		
		String methodName = generateMethodName();
		ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		QuantifiableVariable qv = vars.get(0);
		//OracleVariable var = new OracleVariable(qv.name().toString(), qv.sort());
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		//args.add(var);
		
		String setName = setNames.get(qv.sort());
		
		OracleTerm sub = generateOracle(term.sub(0));
		
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
		
		return new OracleMethod(methodName, args, body);		
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