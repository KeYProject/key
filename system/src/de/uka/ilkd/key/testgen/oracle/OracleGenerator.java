package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
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
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.ReflectionClassCreator;
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
	
	private Set<String> truePredicates;
	
	private Set<String> falsePredicates;
	
	private Set<String> prestateTerms;
	
	private Map<Sort, OracleMethod> invariants;
	
	private List<OracleVariable> methodArgs;

	private Set<Term> constants;
	
	private ReflectionClassCreator rflCreator;
	
	private boolean useRFL;
	
	public static final String PRE_STRING = "_pre";
	
	public OracleGenerator(Services services, ReflectionClassCreator rflCreator, boolean useRFL) {
		this.services = services;
		initOps();		
		oracleMethods = new HashSet<OracleMethod>();
		quantifiedVariables = new LinkedList<OracleVariable>();
		prestateTerms = new HashSet<String>();
		invariants = new HashMap<Sort, OracleMethod>();
		this.rflCreator = rflCreator;
		this.useRFL = useRFL;
		initTrue();
		initFalse();
		methodArgs  = null;
	}
	
	private void initTrue(){
		truePredicates = new HashSet<String>();
		truePredicates.add("inByte");
		truePredicates.add("inChar");
		truePredicates.add("inShort");
		truePredicates.add("inInt");
		truePredicates.add("inLong");
	}
	
	private void initFalse(){
		falsePredicates = new HashSet<String>();
		
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
		
		constants = getConstants(term);
		methodArgs = getMethodArgs(term);
		OracleTerm body = generateOracle(term, false);
		return new OracleMethod("testOracle", methodArgs, "return "+body.toString()+";");
	}
	
	public OracleLocationSet getOracleLocationSet(Term modifierset){
		
		ModifiesSetTranslator mst = new ModifiesSetTranslator(services, this);
		return mst.translate(modifierset);
		
		
	}
	
	
	
	public List<OracleVariable> getMethodArgs() {
		return methodArgs;
	}

	public Set<OracleMethod> getOracleMethods() {
		return oracleMethods;
	}
	
	private boolean isRelevantConstant(Term c){
		Operator op = c.op();
		
		if(isTrueConstant(op) || isFalseConstant(op)){
			return false;
		}
		
		Sort s = c.sort();
		
		Sort nullSort = services.getJavaInfo().getNullType().getSort();
		Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
		Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
		Sort boolSort = services.getTypeConverter().getBooleanLDT().targetSort();
		
		if(s.equals(nullSort)){
			return false;
		}
		
		if(s.extendsTrans(objSort) || s.equals(intSort) || s.equals(boolSort)){
			return true;
		}
		
		return false;
		
	}
	
	private Set<Term> getConstants(Term t){		
		Set<Term> result = new HashSet<Term>();	
		Set<Term> temp = new HashSet<Term>();
		findConstants(temp, t);		
		for(Term c : temp){			
			if(isRelevantConstant(c)){
				result.add(c);
			}			
		}		
		
		return result;		
	}
	
	
	
	public Set<Term> getConstants() {
		return constants;
	}

	private List<OracleVariable> getMethodArgs(Term t){
		
		List<OracleVariable> result = new LinkedList<OracleVariable>();
		
		Sort allIntSort = createSetSort("Integer");
		Sort allBoolSort = createSetSort("Boolean");
		Sort allObjSort = createSetSort("java.lang.Object");
		Sort oldMapSort = new SortImpl(new Name("Map<Object,Object>"));
		
		OracleVariable allInts = new OracleVariable(TestCaseGenerator.ALL_INTS, allIntSort);
		OracleVariable allBools = new OracleVariable(TestCaseGenerator.ALL_BOOLS, allBoolSort);
		OracleVariable allObj = new OracleVariable(TestCaseGenerator.ALL_OBJECTS, allObjSort);
		OracleVariable oldMap = new OracleVariable(TestCaseGenerator.OLDMap, oldMapSort);
		
		for(Term c : constants){
			result.add(new OracleVariable(c.toString(), c.sort()));
			result.add(new OracleVariable(PRE_STRING+c.toString(), c.sort()));
		}
		
		result.add(allBools);
		result.add(allInts);
		result.add(allObj);		
		result.add(oldMap);
		
		return result;
		
	}
	
	
	private void findConstants(Set<Term> constants, Term term){	
		//System.out.println("FindConstants: "+term+ " cls "+term.getClass().getName());
		if(term.op() instanceof Function && term.subs().size() == 0){
			constants.add(term);
		}
		if(term.op() instanceof ProgramVariable){
			constants.add(term);
		}
		
		for(Term sub : term.subs()){
			findConstants(constants, sub);
		}	
		
	}
	
	private Sort createSetSort(String inner){
		String name = "Set<"+inner+">";
		return new SortImpl(new Name(name));
	}


	public OracleTerm generateOracle(Term term, boolean initialSelect){
		
		
		
		Operator op = term.op();
		
		//System.out.println("Translate: "+term+" init: "+initialSelect);
		
		//binary terms
		if(ops.containsKey(op)){			
			OracleTerm left = generateOracle(term.sub(0), initialSelect);
			OracleTerm right = generateOracle(term.sub(1), initialSelect);	
			String javaOp = ops.get(op);
			
			if(javaOp.equals(EQUALS)){
				return eq(left, right);
			}
			else if(javaOp.equals(AND)){
				return and(left,right);
			}
			else if(javaOp.equals(OR)){
				return or(left,right);
			}
			
			
			return new OracleBinTerm(javaOp,left,right);			
		}//negation
		else if(op == Junctor.NOT){
			OracleTerm sub = generateOracle(term.sub(0), initialSelect);
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
			OracleTerm left = generateOracle(term.sub(0), initialSelect);
			OracleTerm right = generateOracle(term.sub(1), initialSelect);
			
			
			
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
			Sort field = services.getTypeConverter().getHeapLDT().getFieldSort();
			Sort heap = services.getTypeConverter().getHeapLDT().targetSort();
			Sort varSort = term.boundVars().get(0).sort();
			if(varSort.equals(field) || varSort.equals(heap)){
				return OracleConstant.TRUE;
			}
			
			OracleMethod method = createQuantifierMethod(term, initialSelect);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			args.addAll(quantifiedVariables);
			args.addAll(methodArgs);
			return new OracleTermCall(method, args);
		}		
		//if-then-else
		else if(op == IfThenElse.IF_THEN_ELSE){
			OracleMethod method = createIfThenElseMethod(term, initialSelect);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			args.addAll(quantifiedVariables);
			args.addAll(methodArgs);
			return new OracleTermCall(method, args);
		}
		//functions
		else if (op instanceof Function) {
			return translateFunction(term, initialSelect);
		}
		//program variables
		else if (op instanceof ProgramVariable){
			ProgramVariable var = (ProgramVariable) op;
			
//			if(services.getVariableNamer().getRenamingMap().get(var) != null){
//				var = services.getVariableNamer().getRenamingMap().get(var);
//			}
			
			//System.out.println(services.getVariableNamer().getRenamingMap());
			
			LocationVariable loc = (LocationVariable) var;
			//System.out.println("Term: "+loc.sort()+" "+loc.name());
			return new OracleConstant(loc.name().toString(), loc.sort());
		}
		
		else{
			//System.out.println("Could not translate: "+term);
			throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
		}
		
	}
	
	private OracleTerm translateFunction(Term term, boolean initialSelect) {
		
	    Operator op = term.op();
		Function fun = (Function) op;
		String name = fun.name().toString();
	    if(isTrueConstant(op)){
	    	return OracleConstant.TRUE;
	    }
	    else if(isFalseConstant(op)){
	    	return OracleConstant.FALSE;
	    }
	    else if(truePredicates.contains(name)){
	    	return OracleConstant.TRUE;
	    }
	    else if(falsePredicates.contains(name)){
	    	return OracleConstant.FALSE;
	    }
	    else if(term.subs().size() == 0){
	    	return new OracleConstant(name, term.sort());
	    }
	    else if(name.endsWith("select")){
	    	
	    	//System.out.println(term+ " init: "+initialSelect);
	    	
	    	return translateSelect(term, initialSelect);	    	
	    }
	    else if(name.equals("arr")){
	    	OracleTerm index = generateOracle(term.sub(0), initialSelect);	    	
	    	return new OracleConstant("["+index+"]", term.sort());	    	
	    }
	    else if(name.equals("length")){
	    	OracleTerm o = generateOracle(term.sub(0), initialSelect);
	    	return new OracleConstant(o + ".length", term.sort());
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
	    			
	    			m = createInvariantMethod(s, initialSelect);
	    			invariants.put(s, m);
	    			oracleMethods.add(m);
	    		}
	    		
	    		Term heap = term.sub(0);	    	
		    	OracleTerm heapTerm  = generateOracle(heap, initialSelect);
		    	
		    	Term object = term.sub(1);
		    	OracleTerm objTerm = generateOracle(object, initialSelect);
		    	
		    	if(isPreHeap(heapTerm)){
		    		if(!objTerm.toString().startsWith(PRE_STRING)){	
		    			prestateTerms.add(objTerm.toString());		    			
		    			objTerm = new OracleConstant(PRE_STRING+object.toString(), object.sort());		    			
		    		}
		    	}	    		
	    		
	    		List<OracleTerm> args = new LinkedList<OracleTerm>();
	    		args.add(objTerm);
	    		args.addAll(quantifiedVariables);
	    		args.addAll(methodArgs);
	    		
	    		return new OracleTermCall(m, args);
	    	}
	    }
	    else if (name.endsWith("::instance")){
	    	
	    	if(fun instanceof SortDependingFunction){
	    		SortDependingFunction sdf  = (SortDependingFunction) fun;
	    		Sort s = sdf.getSortDependingOn();
	    		
	    		
	    		OracleTerm arg = generateOracle(term.sub(0), initialSelect);
	    		OracleType type = new OracleType(s);
	    		
	    		return new OracleBinTerm("instanceof", arg, type);
	    		
	    		
	    	}
	    	
	    	
	    }
	    
	    throw new RuntimeException("Unsupported function found: "+name+ " of type "+fun.getClass().getName());
    }

	private OracleTerm translateSelect(Term term, boolean initialSelect) {
		Term heap = term.sub(0);	    	
		OracleTerm heapTerm  = generateOracle(heap, true);	   	
		
		Term object = term.sub(1);	
		
		OracleTerm objTerm = generateOracle(object, true);
		
		
		
		Term field = term.sub(2);
		OracleTerm fldTerm = generateOracle(field, true);
		String fieldName = fldTerm.toString();
		fieldName = fieldName.substring(fieldName.lastIndexOf(":")+1, fieldName.length());
		fieldName = fieldName.replace("$", "");
		
		String value;
		
		value = createLocationString(heapTerm, objTerm, fieldName, object.sort(), term.sort(), initialSelect);		
		
		if(!initialSelect && isPreHeap(heapTerm)){
			if(term.sort().extendsTrans(services.getJavaInfo().getJavaLangObject().getSort())){
				return new OracleConstant(TestCaseGenerator.OLDMap+".get("+value+")", term.sort());
			}
		}		
		
		return new OracleConstant(value, term.sort());
	}

	private String createLocationString(OracleTerm heapTerm, OracleTerm objTerm, String fieldName,Sort objSort, Sort fieldSort, boolean initialSelect) {
		String value;
		
		String objString =objTerm.toString();
		
		if(isPreHeap(heapTerm)){
			
			if(useRFL){
				if(!objString.startsWith(ReflectionClassCreator.NAME_OF_CLASS)){
					objString = PRE_STRING + objString;
				}			
			}
			else if(initialSelect){
				objString = PRE_STRING + objString;
			}		
			
		}		
		
		if(fieldName.startsWith("[")){
			value = objString+fieldName;
		}else{
			
			if(useRFL){
				
				rflCreator.addSort(objSort);
				rflCreator.addSort(objSort);
				
				value = ReflectionClassCreator.NAME_OF_CLASS +
						"."+
						ReflectionClassCreator.GET_PREFIX+
						ReflectionClassCreator.cleanTypeName(fieldSort.toString())+
						"("+
						objSort+".class, "+
						objString+", "+
						"\""+fieldName+"\""+
						")";						
						
			}
			else{
				value = objString + "."+fieldName;
			}
			
			
			
		}
		return value;
	}

	private boolean isPreHeap(OracleTerm heapTerm) {
		return heapTerm.toString().equals("heapAtPre");
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
		args.addAll(methodArgs);
		
		String body = "return true;";
		
		return new OracleMethod(methodName, args, body);
		
	}
	
	private OracleMethod createInvariantMethod(Sort s, boolean initialSelect){		
		
		String methodName = getSortInvName(s);
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		OracleVariable o = new OracleVariable("o", s);		
		args.add(o);
		args.addAll(methodArgs);
		OracleInvariantTranslator oit = new OracleInvariantTranslator(services);
		Term t = oit.getInvariantTerm(s);
		
		OracleTerm invTerm = generateOracle(t, initialSelect);
		
		String body = "return "+invTerm.toString()+";";
		
		return new OracleMethod(methodName, args, body);
		
		
		
		
	}
	
	private OracleMethod createIfThenElseMethod(Term term, boolean initialSelect){
			
		String methodName = generateMethodName();
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(methodArgs);
		OracleTerm cond = generateOracle(term.sub(0), initialSelect);
		OracleTerm trueCase = generateOracle(term.sub(1), initialSelect);
		OracleTerm falseCase = generateOracle(term.sub(2), initialSelect);
		
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
	
	private OracleMethod createQuantifierMethod(Term term, boolean initialSelect){		
		String methodName = generateMethodName();
		ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		QuantifiableVariable qv = vars.get(0);
		OracleVariable var = new OracleVariable(qv.name().toString(), qv.sort());
				
		String setName = getSetName(qv.sort());
		
		quantifiedVariables.add(var);
		OracleTerm sub = generateOracle(term.sub(0), initialSelect);
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
		
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(quantifiedVariables);
		args.addAll(methodArgs);
		
		
		return new OracleMethod(methodName, args, body);		
	}

	private String createForallBody(QuantifiableVariable qv, String setName,
            OracleNegTerm neg) {
		String tab = TestCaseGenerator.TAB;
	    String body = "\n"+tab+"for("+qv.sort().name()+" "+qv.name()+" : "+setName+"){"
				+ "\n"+tab+tab+"if("+neg.toString()+"){"
				+ "\n"+tab+tab+tab+"return false;"
				+ "\n"+tab+tab+"}"
				+ "\n"+tab+"}"
				+ "\n"+tab+"return true;";
	    return body;
    }	
	
	private String createExistsBody(QuantifiableVariable qv, String setName,
            OracleTerm cond) {
		String tab = TestCaseGenerator.TAB;
	    String body = "\n"+tab+"for("+qv.sort().name()+" "+qv.name()+" : "+setName+"){"
				+ "\n"+tab+tab+"if("+cond.toString()+"){"
				+ "\n"+tab+tab+tab+"return true;"
				+ "\n"+tab+tab+"}"
				+ "\n"+tab+"}"
				+ "\n"+tab+"return false;";
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
	
	private static OracleTerm and(OracleTerm left, OracleTerm right){
		
		
		if(left.equals(OracleConstant.TRUE)){
			return right;
		}
		else if(left.equals(OracleConstant.FALSE)){
			return OracleConstant.FALSE;
		}
		else if(right.equals(OracleConstant.TRUE)){
			return left;
		}
		else if(right.equals(OracleConstant.FALSE)){
			return OracleConstant.FALSE;
		}
		else{
			return new OracleBinTerm(AND, left, right);
		}
		
		
	}
	
	private static OracleTerm or(OracleTerm left, OracleTerm right){
		if(left.equals(OracleConstant.TRUE)){
			return OracleConstant.TRUE;
		}
		else if(left.equals(OracleConstant.FALSE)){
			return right;
		}
		else if(right.equals(OracleConstant.TRUE)){
			return OracleConstant.TRUE;
		}
		else if(right.equals(OracleConstant.FALSE)){
			return left;
		}
		else{
			return new OracleBinTerm(OR, left, right);
		}
	}
	
	
	
}