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
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

public class OracleGenerator {
	
	
	
	private static final String OR = "||";

	private static final String AND = "&&";

	private static final String EQUALS = "==";

	private Services services;
	
	private static int varNum;
	
	private HashMap<Operator, String> ops;


	private Set<OracleMethod> oracleMethods;
	
	private List<OracleVariable> quantifiedVariables;
	
	private Set<String> prestateTerms;
	
	private Map<Sort, OracleMethod> invariants;
	
	public static final String PRE_STRING = "_pre";
	
	public OracleGenerator(Services services) {
		this.services = services;
		initOps();		
		oracleMethods = new HashSet<OracleMethod>();
		quantifiedVariables = new LinkedList<OracleVariable>();
		prestateTerms = new HashSet<String>();
		invariants = new HashMap<Sort, OracleMethod>();
	}

	
	private void initOps(){
		ops = new HashMap<Operator,String>();		
		ops.put(Equality.EQV, EQUALS);
		ops.put(Equality.EQUALS, EQUALS);
		ops.put(Junctor.AND, AND);
		ops.put(Junctor.OR, OR);
		ops.put(services.getTypeConverter().getIntegerLDT().getLessOrEquals(), "<=");
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
	
	public OracleMethod generateOracleMethod(Term term){
		OracleTerm body = generateOracle(term);
		return new OracleMethod("testOracle", new LinkedList<OracleVariable>(), "return "+body.toString()+";");
	}
	
	
	
	public Set<OracleMethod> getOracleMethods() {
		return oracleMethods;
	}


	public OracleTerm generateOracle(Term term){
		Operator op = term.op();
		
		//System.out.println("Translate: "+term+" "+term.op().toString());
		
		//binary terms
		if(ops.containsKey(op)){			
			OracleTerm left = generateOracle(term.sub(0));
			OracleTerm right = generateOracle(term.sub(1));	
			String javaOp = ops.get(op);
			
			if(javaOp.equals(EQUALS)){
				return eq(left, right);
			}
			
			
			return new OracleBinTerm(javaOp,left,right);			
		}//negation
		else if(op == Junctor.NOT){
			OracleTerm sub = generateOracle(term.sub(0));
			if(sub instanceof OracleNegTerm){
				OracleNegTerm neg = (OracleNegTerm) sub;
				return neg.getSub();
			}
			return new OracleNegTerm(sub);
		}
		//true
		else if (op == Junctor.TRUE) {
			return OracleConstant.TRUE;
		}
		//false
		else if (op == Junctor.FALSE) {
			return OracleConstant.FALSE;
		}
		else if (op == Junctor.IMP){
			OracleTerm left = generateOracle(term.sub(0));
			OracleTerm right = generateOracle(term.sub(1));
			
			
			
			OracleTerm notLeft = neg(left);
			return new OracleBinTerm(OR, notLeft, right);
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
		//program variables
		else if (op instanceof ProgramVariable){
			LocationVariable loc = (LocationVariable) op;
			//System.out.println("Term: "+loc.sort()+" "+loc.name());
			return new OracleConstant(loc.name().toString(), loc.sort());
		}
		
		else{
			System.out.println("Could not translate: "+term);
			throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
		}
		
	}

	private OracleTerm translateFunction(Term term) {
	    Operator op = term.op();
		Function fun = (Function) op;
		String name = fun.name().toString();
	    if(isTrueConstant(op)){
	    	return OracleConstant.TRUE;
	    }
	    else if(isFalseConstant(op)){
	    	return OracleConstant.FALSE;
	    }
	    else if(term.subs().size() == 0){
	    	return new OracleConstant(name, term.sort());
	    }
	    else if(name.endsWith("select")){
	    	
	    	Term heap = term.sub(0);	    	
	    	OracleTerm heapTerm  = generateOracle(heap);	    	
	    	
	    	Term object = term.sub(1);
	    	OracleTerm objTerm = generateOracle(object);
	    	
	    	Term field = term.sub(2);
	    	OracleTerm fldTerm = generateOracle(field);
	    	String fieldName = fldTerm.toString();
	    	fieldName = fieldName.substring(fieldName.lastIndexOf(":")+1, fieldName.length());
	    	fieldName = fieldName.replace("$", "");
	    	String value = objTerm.toString() + "."+fieldName;
	    	
	    	
	    	if(heapTerm.toString().equals("heapAtPre")){
	    		
	    		if(value.startsWith(PRE_STRING)){
	    			String sub = value.substring(PRE_STRING.length(), value.length());	    			
	    			prestateTerms.add(sub);
	    		}
	    		else{
	    			prestateTerms.add(value);
	    		}
	    		
	    		
	    		if(!objTerm.toString().startsWith(PRE_STRING)){
	    			
	    			return new OracleConstant(PRE_STRING+value, term.sort());
	    		}
	    	}
	    	
	    	
	    	return new OracleConstant(value, term.sort());	    	
	    }
	    else if(name.endsWith("::<inv>")){	    	
	    	if(fun instanceof IObserverFunction){
	    		IObserverFunction obs = (IObserverFunction) fun;
	    		
	    		Sort s = obs.getContainerType().getSort();
	    		OracleMethod m;
	    		
	    		if(invariants.containsKey(s)){
	    			m = invariants.get(s);
	    		}
	    		else{
	    			//needed for recursive invariants
	    			m = createDummyInvariant(s);
	    			invariants.put(s, m);
	    			
	    			m = createInvariantMethod(s);
	    			invariants.put(s, m);
	    			oracleMethods.add(m);
	    		}
	    		
	    		Term heap = term.sub(0);	    	
		    	OracleTerm heapTerm  = generateOracle(heap);
		    	
		    	Term object = term.sub(1);
		    	OracleTerm objTerm = generateOracle(object);
		    	
		    	if(heapTerm.toString().equals("heapAtPre")){
		    		if(!objTerm.toString().startsWith(PRE_STRING)){	
		    			prestateTerms.add(objTerm.toString());		    			
		    			objTerm = new OracleConstant(PRE_STRING+object.toString(), object.sort());		    			
		    		}
		    	}	    		
	    		
	    		List<OracleTerm> args = new LinkedList<OracleTerm>();
	    		args.add(objTerm);
	    		
	    		return new OracleTermCall(m, args);
	    	}
	    }
	    else if (name.endsWith("::instance")){
	    	
	    	if(fun instanceof SortDependingFunction){
	    		SortDependingFunction sdf  = (SortDependingFunction) fun;
	    		Sort s = sdf.getSortDependingOn();
	    		
	    		
	    		OracleTerm arg = generateOracle(term.sub(0));
	    		OracleType type = new OracleType(s);
	    		
	    		return new OracleBinTerm("instanceof", arg, type);
	    		
	    		
	    	}
	    	
	    	
	    }
	    
	    throw new RuntimeException("Unsupported function found: "+name+ " of type "+fun.getClass().getName());
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
	
	private String getSortInvName(Sort s){
		String sortName = s.name().toString();
		sortName = sortName.replace(".", "");
		
		String methodName = "inv_"+sortName;
		
		return methodName;
	}
	
	private OracleMethod createDummyInvariant(Sort s){
		String methodName = getSortInvName(s);
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		OracleVariable o = new OracleVariable("o", s);		
		args.add(o);
		
		String body = "return true;";
		
		return new OracleMethod(methodName, args, body);
		
	}
	
	private OracleMethod createInvariantMethod(Sort s){		
		
		String methodName = getSortInvName(s);
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		OracleVariable o = new OracleVariable("o", s);		
		args.add(o);
		
		OracleInvariantTranslator oit = new OracleInvariantTranslator(services);
		Term t = oit.getInvariantTerm(s);
		
		OracleTerm invTerm = generateOracle(t);
		
		String body = "return "+invTerm.toString()+";";
		
		return new OracleMethod(methodName, args, body);
		
		
		
		
	}
	
	private OracleMethod createIfThenElseMethod(Term term){
			
		String methodName = generateMethodName();
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		
		OracleTerm cond = generateOracle(term.sub(0));
		OracleTerm trueCase = generateOracle(term.sub(1));
		OracleTerm falseCase = generateOracle(term.sub(2));
		
		String body = "if("+cond+"){"
				+ "\n   return "+trueCase+";"
				+ "\n}else{"
				+ "\n   return "+falseCase+";"
				+ "\n}";
		
		return new OracleMethod(methodName, args, body, term.sort());		
		
	}
	
	
	
	public Set<String> getPrestateTerms() {
		return prestateTerms;
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
	
	private static OracleTerm neg(OracleTerm t){
		
		if(t instanceof OracleNegTerm){			
			return ((OracleNegTerm) t).getSub();
		}
		else{
			return new OracleNegTerm(t);
		}
		
	}
	
	private static OracleTerm eq(OracleTerm left, OracleTerm right){
		if(left.equals(OracleConstant.TRUE)){
			return right;
		}
		else if(left.equals(OracleConstant.FALSE)){
			return neg(right);
		}
		else if(right.equals(OracleConstant.TRUE)){
			return left;
		}
		else if(right.equals(OracleConstant.FALSE)){
			return neg(left);
		}
		else{
			return new OracleBinTerm(EQUALS, left, right);
		}
	}
	
	
	
}