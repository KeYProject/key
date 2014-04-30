// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.hierarchy.SortNode;
import de.uka.ilkd.key.smt.hierarchy.TypeHierarchy;
import de.uka.ilkd.key.smt.lang.SMTFile;
import de.uka.ilkd.key.smt.lang.SMTFunction;
import de.uka.ilkd.key.smt.lang.SMTFunctionDef;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.SMTTerm;
import de.uka.ilkd.key.smt.lang.SMTTermCall;
import de.uka.ilkd.key.smt.lang.SMTTermITE;
import de.uka.ilkd.key.smt.lang.SMTTermMultOp;
import de.uka.ilkd.key.smt.lang.SMTTermNumber;
import de.uka.ilkd.key.smt.lang.SMTTermVariable;
import de.uka.ilkd.key.smt.lang.Util;
import de.uka.ilkd.key.util.Debug;

public class SMTObjTranslator implements SMTTranslator {

	public static final String CLASS_INVARIANT = "classInvariant";
	public static final String LENGTH = "length";
	private static final String WELL_FORMED_NAME = "wellFormed";
	public static final String BINT_SORT = "IntB";
	public static final String HEAP_SORT = "Heap";
	public static final String FIELD_SORT = "Field";
	public static final String LOCSET_SORT = "LocSet";
	public static final String OBJECT_SORT = "Object";
	public static final String ANY_SORT = "Any";
	public static final String SEQ_SORT = "SeqB";
	private static final String NULL_CONSTANT = "null";
	private static final String EMPTY_CONSTANT = "empty";
	public static final String ELEMENTOF = "elementOf";
	private static final String SELECT = "select";
	private static final String CREATED_FIELD_NAME = "java.lang.Object::<created>";
	private static final String ARR_FUNCTION_NAME = "arr";
	private static final String SEQ_EMPTY = "seqEmpty";
	private static final String SEQ_OUTSIDE = "seqGetOutside";
	public static final String SEQ_GET = "seqGet";
	public static final String SEQ_LEN = "seqLen";
	/**
	 * Mapps some basic KeY operators to their equivalent built in operators.
	 * Initialized in initOpTable.
	 */
	private Map<Operator, SMTTermMultOp.Op> opTable;

	private int varNr;


	/**
	 * The SMT translation settings.
	 */
	private SMTSettings settings;
	/**
	 * KeY services provide a lot of useful stuff.
	 */
	private Services services;
	/**
	 * Assertions regarding Any2Object, Any2BInt, Object2Any, etc. functions.
	 */
	private List<SMTTerm> castAssertions;
	/**
	 * Assertions regarding the wellformed function.
	 */
	private List<SMTTerm> wellFormedAssertions;
	/**
	 * The select function.
	 * select : Heap x Object x Field -> Any
	 */
	private SMTFunction selectFunction;
	/**
	 * The wellformed predicate.
	 * wellformed : Heap -> Bool
	 */
	private SMTFunction wellformedFunction;
	/**
	 * The SMT sorts used in this translation.
	 * Use the String constants LOCSET_SORT, HEAP_SORT, etc. to get wanted sort.
	 * Initialized in 
	 */
	private Map<String, SMTSort> sorts;
	/**
	 * Type bits for the SMTSorts that are subtypes of any.
	 */
	private Map<SMTSort, SMTTermNumber> sortNumbers;
	/**
	 * Stores the sort of each field. First column is field name, second is
	 * field sort.
	 */
	private Map<String,Sort> fieldSorts;

	/**
	 * Type predicates used to specify the java type hierarchy.
	 * Maps the name of the type Predicate function, which is unique 
	 * for each sort to its SMTFunction. This way we ensure that we do 
	 * not have 2 identical type predicates.
	 */
	private Map<String, SMTFunction> typePredicates;
	/**
	 * Assertions for specifying the java type hierarchy.
	 * First column is the java type, second column the assertion.
	 */
	private Map<String, SMTTerm> typeAssertions;
	/**
	 * Assertions regarding the return type of functions.
	 * If a function returns a type T, then we state that 
	 * for all possible arguments, the function call is of type T.
	 */
	private List<SMTTerm> functionTypeAssertions;
	/**
	 * The java sorts that we have encountered in the proof obligation.
	 */
	private Set<Sort> javaSorts;
	/**
	 * The java sorts that we encountered in the proof obligation and all their supersorts.
	 */
	private Set<Sort> extendedJavaSorts;
	/**
	 * The functions that we declare are stored here.
	 */
	private Map<String, SMTFunction> functions;
	/**
	 * Stores the order in which the function definitions should be 
	 * written in the SMT file. If the id of f1 appears before the
	 * id of f2 in this list, f1 will be written before f2.
	 */
	private List<String> functionDefinitionOrder;

	/**
	 * The null constant.
	 */
	private SMTTerm nullConstant;
	/**
	 * The empty constant.
	 */
	private SMTTerm emptyConstant;
	/**
	 * List of current quantified variables.
	 */
	private List<SMTTermVariable> quantifiedVariables;
	/**
	 * Overflow guards for ground terms.
	 */
	private Set<SMTTerm> overflowGuards;
	/**
	 * The java type hierarchy.
	 */
	private TypeHierarchy thierarchy;
	/**
	 * The concrete java type hierarchy obtained by
	 * contracting all abstract types from the java 
	 * type hierarchy.
	 */
	private TypeHierarchy concreteHierarchy;
	/**
	 * Types information needed by the counterexample formatter.
	 */
	private ProblemTypeInformation types;
	/**
	 * The query that will extract the counterexample from the z3 solver.
	 */
	private ModelExtractor query = new ModelExtractor();

	//some special KeY sorts
	private Sort integerSort;
	private Sort heapSort;
	private Sort fieldSort;
	private Sort locsetSort;
	private Sort boolSort;
	private Sort seqSort;

	/**
	 * The elementOf predicate.
	 */
	private SMTFunction elementOfFunction;
	/**
	 * The constant counter counts the number of heap and field constants in order
	 *  to determine the size of their sorts.
	 */
	private ConstantCounter cc;
	/**
	 * If true, guards for preventing integer overflows will be added.
	 */
	private static boolean guardOverflow = true;


	public SMTObjTranslator(SMTSettings settings, Services services) {
		super();
		this.settings = settings;
		this.services = services;
		types = new ProblemTypeInformation(services);
		initSorts();
		initOpTable();
		overflowGuards = new HashSet<SMTTerm>();
		typePredicates = new HashMap<String, SMTFunction>();
		functions = new HashMap<String, SMTFunction>();
		quantifiedVariables = new LinkedList<SMTTermVariable>();
		functionTypeAssertions = new LinkedList<SMTTerm>();
		functionDefinitionOrder = new LinkedList<String>();
		new LinkedList<SMTTerm>();
		javaSorts = new HashSet<Sort>();
		extendedJavaSorts = new HashSet<Sort>();
		thierarchy = new TypeHierarchy(services);
		concreteHierarchy = new TypeHierarchy(services);
		concreteHierarchy.removeInterfaceNodes();
		typeAssertions = new HashMap<String, SMTTerm>();
		new LinkedList<SMTTerm>();
		new LinkedList<SMTTerm>();
		fieldSorts = new HashMap<String,Sort>();
		wellFormedAssertions = new LinkedList<SMTTerm>();
	}

	/**
	 * Creates some special constant functions, which are used in every translation.
	 */
	private void createSpecialFunctions() {
		nullConstant = createNullConstant();
		castAssertions = new LinkedList<SMTTerm>();
		selectFunction = createSelectFunction();		
		wellformedFunction = createWellFormedFunction();
		elementOfFunction = createElementOfFunction();
		emptyConstant = createEmptyConstant();		
		createLengthFunction();
		createArrFunction();
		createSeqConstantsAndAssertions();
		createCreatedConstant();
		createClassInvariantFunction();
	}

	/**
	 * @return the types
	 */
	public ProblemTypeInformation getTypes() {
		return types;
	}

	/**
	 * Creates the arr function.
	 */
	private void createArrFunction() {
		String id = ARR_FUNCTION_NAME;
		List<SMTSort> domain = new LinkedList<SMTSort>();
		domain.add(sorts.get(BINT_SORT));
		SMTSort image = sorts.get(FIELD_SORT);
		SMTFunction f = new SMTFunction(id,domain,image);
		functions.put(id, f);
	}

	/**
	 * Creates the select function.
	 */
	private SMTFunction createSelectFunction() {
		String id = SELECT;

		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		domainSorts.add(sorts.get(HEAP_SORT));
		domainSorts.add(sorts.get(OBJECT_SORT));
		domainSorts.add(sorts.get(FIELD_SORT));

		SMTSort imageSort = sorts.get(ANY_SORT);

		SMTFunction f = new SMTFunction(id, domainSorts, imageSort);
		//System.err.println("ADD Function:"+f);
		functions.put(SELECT, f);

		return f;
	}
	/**
	 * Creates the elementOf function.
	 */
	private SMTFunction createElementOfFunction() {
		String id = ELEMENTOF;

		List<SMTSort> domainSorts = new LinkedList<SMTSort>();

		domainSorts.add(sorts.get(OBJECT_SORT));
		domainSorts.add(sorts.get(FIELD_SORT));
		domainSorts.add(sorts.get(LOCSET_SORT));

		SMTSort imageSort = SMTSort.BOOL;

		SMTFunction f = new SMTFunction(id, domainSorts, imageSort);
		//System.err.println("ADD Function:"+f);
		functions.put(ELEMENTOF, f);

		return f;
	}

	/**
	 * Creates the length function.
	 */
	private SMTFunction createLengthFunction(){

		String id = LENGTH;

		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		domainSorts.add(sorts.get(OBJECT_SORT));

		SMTSort imageSort = sorts.get(BINT_SORT);
		SMTFunction f = new SMTFunction(id, domainSorts, imageSort);
		//System.err.println("ADD Function:"+f);
		functions.put(LENGTH, f);

		return f;

	}

	/**
	 * Creates the wellformed function.
	 */
	private SMTFunction createWellFormedFunction(){
		String id = WELL_FORMED_NAME;
		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		domainSorts.add(sorts.get(HEAP_SORT));
		SMTSort imageSort = SMTSort.BOOL;
		SMTFunction f = new SMTFunction(id, domainSorts, imageSort);

		functions.put(WELL_FORMED_NAME, f);

		return f;

	}

	/**
	 * Fills the operator table.
	 */
	private void initOpTable() {
		opTable = new HashMap<Operator, SMTTermMultOp.Op>();
		opTable.put(Junctor.AND, SMTTermMultOp.Op.AND);
		opTable.put(Junctor.OR, SMTTermMultOp.Op.OR);
		opTable.put(Junctor.IMP, SMTTermMultOp.Op.IMPLIES);
		opTable.put(Equality.EQUALS, SMTTermMultOp.Op.EQUALS);
		opTable.put(Equality.EQV, SMTTermMultOp.Op.EQUALS);
		opTable.put(services.getTypeConverter().getIntegerLDT().getLessThan(),
				SMTTermMultOp.Op.BVSLT);
		opTable.put(services.getTypeConverter().getIntegerLDT()
				.getLessOrEquals(), SMTTermMultOp.Op.BVSLE);
		opTable.put(services.getTypeConverter().getIntegerLDT()
				.getGreaterThan(), SMTTermMultOp.Op.BVSGT);
		opTable.put(services.getTypeConverter().getIntegerLDT()
				.getGreaterOrEquals(), SMTTermMultOp.Op.BVSGE);
		opTable.put(services.getTypeConverter().getIntegerLDT().getAdd(),
				SMTTermMultOp.Op.PLUS);
		opTable.put(services.getTypeConverter().getIntegerLDT().getSub(),
				SMTTermMultOp.Op.MINUS);
		opTable.put(services.getTypeConverter().getIntegerLDT().getMul(),
				SMTTermMultOp.Op.MUL);
		opTable.put(services.getTypeConverter().getIntegerLDT().getDiv(),
				SMTTermMultOp.Op.BVSDIV);
	}

	/**
	 * Get special KeY sorts that we need.
	 */
	private void initSorts() {

		// KeY Sorts
		seqSort = services.getTypeConverter().getSeqLDT().targetSort();
		integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
		heapSort = services.getTypeConverter().getHeapLDT().targetSort();
		fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
		locsetSort = services.getTypeConverter().getLocSetLDT().targetSort();
		boolSort = services.getTypeConverter().getBooleanLDT().targetSort();

		cc = new ConstantCounter();

	}

	/**
	 * Create the needed SMT sorts.
	 */
	private void initSMTSorts() {
		sorts = new HashMap<String, SMTSort>();
		sortNumbers = new HashMap<SMTSort, SMTTermNumber>();
		long maxSize = 0;

		//Bounded Integer
		SMTSort smtBoundedInt = new SMTSort(BINT_SORT);
		smtBoundedInt.setBitSize(settings.getIntBound());
		maxSize = Math.max(maxSize, smtBoundedInt.getBitSize());
		sorts.put(BINT_SORT, smtBoundedInt);
		sortNumbers.put(smtBoundedInt, new SMTTermNumber(5, 3,sorts.get(BINT_SORT)));

		// Heap
		SMTSort heap = new SMTSort(HEAP_SORT);

		int heapBound = cc.getHeaps().size();


		heap.setBound(heapBound);

		if(heap.getBitSize() < 1){
			heap.setBitSize(1);
		}


		maxSize = Math.max(maxSize, heap.getBitSize());
		sorts.put(HEAP_SORT, heap);
		sortNumbers.put(heap, new SMTTermNumber(1, 3,sorts.get(BINT_SORT)));

		// Field
		SMTSort field = new SMTSort(FIELD_SORT);
		field.setBound(cc.getFields().size() + smtBoundedInt.getBound());
		sorts.put(FIELD_SORT, field);
		sortNumbers.put(field, new SMTTermNumber(2, 3,sorts.get(BINT_SORT)));


		// LocSet
		SMTSort locset = new SMTSort(LOCSET_SORT);

		locset.setBitSize(settings.getLocSetBound());

		maxSize = Math.max(maxSize, locset.getBitSize());
		sorts.put(LOCSET_SORT, locset);
		sortNumbers.put(locset, new SMTTermNumber(4, 3,sorts.get(BINT_SORT)));
		// Object
		SMTSort object = new SMTSort(OBJECT_SORT);
		object.setBitSize(settings.getObjectBound());
		maxSize = Math.max(maxSize, object.getBitSize());
		sorts.put(OBJECT_SORT, object);
		sortNumbers.put(object, new SMTTermNumber(3, 3,sorts.get(BINT_SORT)));



		//Seq

		SMTSort seq = new SMTSort(SEQ_SORT);
		seq.setBitSize(settings.getSeqBound());
		maxSize = Math.max(maxSize, seq.getBitSize());
		sorts.put(SEQ_SORT, seq);
		sortNumbers.put(seq, new SMTTermNumber(7, 3,sorts.get(BINT_SORT)));


		// Any
		SMTSort any = new SMTSort(ANY_SORT);
		any.setBitSize((int) (maxSize + 3));
		sorts.put(ANY_SORT, any);
		sortNumbers.put(any, new SMTTermNumber(6, 3,sorts.get(BINT_SORT)));



		// don't forget the bool sort number!!
		sortNumbers.put(SMTSort.BOOL, new SMTTermNumber(0, 3,sorts.get(BINT_SORT)));
	}

	@Override
	public StringBuffer translateProblem(Term problem, Services services,
			SMTSettings settings) throws IllegalFormulaException {
		this.settings = settings;
		this.services = services;
		SMTFile file = translateProblem(problem);
		String s = file.toString();
		//SolverQueryer q = new SolverQueryer();
		//s += "\n" + q.getQuery();
		return new StringBuffer(s);
	}

	public ModelExtractor getQuery(){
		for (String str : functions.keySet()) {
			SMTFunction f = functions.get(str);
			query.addFunction(f);
		}
		types.setServices(services);
		types.setJavaSorts(extendedJavaSorts);
		types.setSettings(settings);
		types.setSortNumbers(sortNumbers);
		types.setSorts(sorts);
		query.setIntBound((int) settings.getIntBound());
		query.setTypes(types);
		return query;
	}
	/**
	 * Creates the null constant.
	 * @return
	 */
	private SMTTerm createNullConstant() {
		SMTFunction f = new SMTFunction(NULL_CONSTANT,
				new LinkedList<SMTSort>(), sorts.get(OBJECT_SORT));

		SMTTerm zero = new SMTTermNumber(0, settings.getObjectBound(), sorts.get(OBJECT_SORT));

		SMTFunctionDef def = new SMTFunctionDef(f, new LinkedList<SMTTermVariable>(), zero);

		def.setComment("This function is dedicated to Mattias, who has insisted for a long time that the null object should always be object 0.");

		functions.put(NULL_CONSTANT, def);
		functionDefinitionOrder.add(NULL_CONSTANT);
		types.putConstantType(Util.processName(NULL_CONSTANT), sorts.get(OBJECT_SORT));

		return SMTTerm.call(def);
	}
	/**
	 * Creates the necessary sequence functions and assertions.
	 */
	private void createSeqConstantsAndAssertions(){
		//seq empty
		SMTFunction seqEmpty = new SMTFunction(SEQ_EMPTY, new LinkedList<SMTSort>(), sorts.get(SEQ_SORT));
		functions.put(SEQ_EMPTY, seqEmpty);
		types.putConstantType(SEQ_EMPTY, sorts.get(SEQ_SORT));
		//seq outside
		SMTFunction outside = new SMTFunction(SEQ_OUTSIDE, new LinkedList<SMTSort>(), sorts.get(ANY_SORT));
		functions.put(SEQ_OUTSIDE, outside);
		types.putConstantType(SEQ_OUTSIDE, sorts.get(ANY_SORT));

		List<SMTSort> getDomain = new LinkedList<SMTSort>();
		getDomain.add(sorts.get(SEQ_SORT));
		getDomain.add(sorts.get(BINT_SORT));
		//seqget
		SMTFunction seqGet = new SMTFunction(SEQ_GET, getDomain, sorts.get(ANY_SORT));
		functions.put(SEQ_GET, seqGet);

		List<SMTSort> lenDomain = new LinkedList<SMTSort>();
		lenDomain.add(sorts.get(SEQ_SORT));
		//seqlen
		SMTFunction seqLen = new SMTFunction(SEQ_LEN,lenDomain,sorts.get(BINT_SORT));
		functions.put(SEQ_LEN, seqLen);

		//Assertion 1: length >= 0

		SMTTermVariable i = new SMTTermVariable("i", sorts.get(BINT_SORT));
		SMTTermVariable s = new SMTTermVariable("s", sorts.get(SEQ_SORT));

		SMTTerm lenS = SMTTerm.call(functions.get(SEQ_LEN),s);
		SMTTerm zero = new SMTTermNumber(0, settings.getIntBound(), sorts.get(BINT_SORT));
		SMTTerm axiom1 = lenS.gte(zero);			
		axiom1 = axiom1.forall(s);

		axiom1.setComment("All sequents have length >= 0");

		functionTypeAssertions.add(axiom1);

		//Assertion 2: out of bounds -> outside

		SMTTerm getS = SMTTerm.call(functions.get(SEQ_GET),s,i);
		SMTTerm left = i.lt(zero).or(lenS.lte(i));
		SMTTerm right = getS.equal(SMTTerm.call(functions.get(SEQ_OUTSIDE)));
		SMTTerm axiom2 = left.implies(right);

		List<SMTTermVariable> a2vars = new LinkedList<SMTTermVariable>();
		a2vars.add(s);
		a2vars.add(i);

		axiom2 = axiom2.forall(a2vars);		
		axiom2.setComment("Index out of bounds implies seqGetOutside");
		functionTypeAssertions.add(axiom2);

		//Assertion 3:extensionality

		//		TermVariable s2 = new TermVariable("s2", sorts.get(SEQ_SORT));
		//		
		//		SMTTerm lenS2 = SMTTerm.call(functions.get(SEQ_LEN), s2);
		//		SMTTerm getS2 = SMTTerm.call(functions.get(SEQ_GET),s2,i);
		//		SMTTerm eqLengths = lenS.equal(lenS2);
		//		SMTTerm eqContent = getS.equal(getS2);
		//		
		//		eqContent = eqContent.forall(i);
		//		
		//		SMTTerm a3right = eqLengths.and(eqContent);
		//		SMTTerm a3left = s.equal(s2);
		//		
		//		SMTTerm axiom3 = a3left.equal(a3right);
		//		
		//		List<TermVariable> a3vars = new LinkedList<TermVariable>();
		//		a3vars.add(s);
		//		a3vars.add(s2);
		//		
		//		axiom3 = axiom3.forall(a3vars);
		//		axiom3.setComment("Extensionality for sequents");
		//		functionTypeAssertions.add(axiom3);

		//Axiom 4: length of empty is 0
		SMTTerm lenEmpty = SMTTerm.call(functions.get(SEQ_LEN), SMTTerm.call(functions.get(SEQ_EMPTY)));

		SMTTerm axiom4 = lenEmpty.equal(zero);	
		axiom4.setComment("Length of seqEmpty is 0");
		functionTypeAssertions.add(axiom4);

	}
	/**
	 * Creates the empty constant.
	 * @return
	 */
	private SMTTerm createEmptyConstant(){
		SMTFunction f = new SMTFunction(EMPTY_CONSTANT,
				new LinkedList<SMTSort>(), sorts.get(LOCSET_SORT));
		functions.put(EMPTY_CONSTANT, f);
		SMTTerm empty = SMTTerm.call(f);

		SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));
		SMTTermVariable v = new SMTTermVariable("f", sorts.get(FIELD_SORT));

		SMTTerm elementOfEmpty = SMTTerm.call(elementOfFunction, o, v, empty);

		SMTTerm sub = elementOfEmpty.not();

		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.add(o);
		vars.add(v);

		SMTTerm assertion = SMTTerm.forall(vars, sub, null);

		functionTypeAssertions.add(assertion);
		types.putConstantType(Util.processName(EMPTY_CONSTANT), sorts.get(LOCSET_SORT));




		return empty;
	}
	/**
	 * Creates assertion which states that the length of each object is greater than or equal to 0.
	 */
	private void generateLengthAssertions(){

		SMTFunction length = functions.get(LENGTH);
		SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));
		SMTTerm call = SMTTerm.call(length, o);
		SMTTermNumber zero = new SMTTermNumber(0, settings.getIntBound(), sorts.get(BINT_SORT));
		SMTTerm gtzero = call.gte(zero);
		SMTTerm assertion1 = SMTTerm.forall(o, gtzero, null);

		assertion1.setComment("Assert that all lengths are positive");
		functionTypeAssertions.add(assertion1);

		//		SMTTerm isArray = SMTTerm.FALSE;
		//		for(Sort s :thierarchy.getArraySortList()){
		//			String name = s.name().toString();
		//			SMTFunction type = getTypePredicate(name);
		//			if(type!=null){
		//
		//				SMTTerm callType = SMTTerm.call(type,o);
		//				isArray = isArray.or(callType);
		//
		//			}
		//		}
		//
		//		SMTTerm isNotArray = isArray.not();
		//
		//		SMTTerm sub = isNotArray.implies(call.equal(zero));
		//
		//		SMTTerm assertion2 = SMTTerm.forall(o, sub, null);
		//		assertion2.setComment("Assert that non array types have length zero");


		//		functionTypeAssertions.add(assertion2);




	}
	/**
	 * Creates an SMT constant for each named field pointing to a distinct value.
	 * Creates the arr function.
	 */
	private void generateFieldFunctionDefinitions() {

		List<SMTFunction> fieldConstants = new LinkedList<SMTFunction>();
		// also dynamically calculate bound for field
		int bound = 0;
		for (String s : functions.keySet()) {
			SMTFunction f = functions.get(s);
			if (f.getDomainSorts().size() == 0
					&& f.getImageSort().getId().equals(FIELD_SORT)) {
				fieldConstants.add(f);
				++bound;
			}
		}

		//System.out.println("Found "+bound+" field constants");

		SMTSort field = sorts.get(FIELD_SORT);
		long intSize = settings.getIntBound();
		long fieldSize = field.getBitSize();

		//compute bitsize for sort field		
		field.setBitSize(intSize);
		field.setBound(field.getBound()+bound);
		fieldSize = field.getBitSize();
		//create function definition for all named fields
		long i = (long) Math.pow(2, intSize);
		for (SMTFunction f : fieldConstants) {
			SMTTermNumber fieldarg = new SMTTermNumber(i++,fieldSize,sorts.get(BINT_SORT));
			SMTFunctionDef fieldConstant = new SMTFunctionDef(f, new LinkedList<SMTTermVariable>(), fieldarg);
			String id = f.getId();

			if(!functions.containsKey(id)){
				id = id.replace("|", "");

			}
			functions.put(id, fieldConstant);
			functionDefinitionOrder.add(id);


		}
		//create arr function def
		SMTTermVariable intarg = new SMTTermVariable(varName('i'), sorts.get(BINT_SORT));
		long diff = fieldSize - intSize;

		SMTTermNumber bitDiff = new SMTTermNumber(0,diff,sorts.get(BINT_SORT));
		SMTTerm sub = bitDiff.concat(intarg);

		SMTFunctionDef arr = new SMTFunctionDef(ARR_FUNCTION_NAME, intarg, field, sub);
		functions.put(ARR_FUNCTION_NAME, arr);
		functionDefinitionOrder.add(ARR_FUNCTION_NAME);
	}
	/**
	 * Creates the wellformed function definition.
	 */
	private void generateWellFormedAssertions(){

		//Assertion 1: 

		SMTTermVariable h = new SMTTermVariable("h", sorts.get(HEAP_SORT));
		SMTTermVariable o = new SMTTermVariable("o",sorts.get(OBJECT_SORT));
		SMTTermVariable f = new SMTTermVariable("f", sorts.get(FIELD_SORT));
		SMTTermVariable o1 = new SMTTermVariable("o1",sorts.get(OBJECT_SORT));
		SMTTermVariable f1 = new SMTTermVariable("f1", sorts.get(FIELD_SORT));
		SMTTermVariable bi = new SMTTermVariable(varName('i'), sorts.get(BINT_SORT));



		List<SMTTerm> vars = new LinkedList<SMTTerm>();
		vars.add(h);
		vars.add(o);
		vars.add(f);



		//wellformed(h)
		//SMTTerm left;
		//select(h,o,f)
		SMTTerm select = SMTTerm.call(selectFunction, vars);
		//isObject(select(h,o,f))
		//SMTTerm isObject = SMTTerm.call(getIsFunction(sorts.get(OBJECT_SORT)),select);
		//wellformed(h) and isObject(select(h,o,f))
		//left = isObject;

		//any2obj(select(h,o,f))		
		SMTTerm selectObj = castTermIfNecessary(select, sorts.get(OBJECT_SORT));
		//any2obj(select(h,o,f)) == null
		SMTTerm right = selectObj.equal(nullConstant);
		//created





		SMTTerm created = SMTTerm.call(functions.get(CREATED_FIELD_NAME));

		List<SMTTerm> args = new LinkedList<SMTTerm>();		
		args.add(h);
		args.add(selectObj);
		args.add(created);
		//select(h,any2obj(select(h,o,f)),created)
		SMTTerm selectCreated = SMTTerm.call(selectFunction,args);
		SMTTerm selectCreatedBool = castTermIfNecessary(selectCreated, SMTSort.BOOL);

		right = right.or(selectCreatedBool);

		SMTTerm assertion1 = right;

		List<SMTTermVariable> assertion1Vars = new LinkedList<SMTTermVariable>();
		assertion1Vars.add(o);
		assertion1Vars.add(f);
		assertion1 = SMTTerm.forall(assertion1Vars, assertion1, null);



		//Assertion 2 - locset


		SMTFunction isLocSetFun = getIsFunction(sorts.get(LOCSET_SORT));
		SMTTerm isLocSetTErm = SMTTerm.call(isLocSetFun, select);

		SMTTerm left2 = isLocSetTErm;

		SMTTerm selectLocSet = castTermIfNecessary(select, sorts.get(LOCSET_SORT));
		SMTTerm elementOfTerm = SMTTerm.call(elementOfFunction, o1,f1,selectLocSet);

		left2 = elementOfTerm;

		SMTTerm right2 = o1.equal(nullConstant);

		SMTTerm selectCreated2 = SMTTerm.call(selectFunction,h,o1,created);
		SMTTerm selectCreatedBool2 = castTermIfNecessary(selectCreated2, SMTSort.BOOL);

		right2 = right2.or(selectCreatedBool2);

		List<SMTTermVariable> forallVariables = new LinkedList<SMTTermVariable>();
		//forallVariables.add(h);
		forallVariables.add(o);
		forallVariables.add(f);
		forallVariables.add(o1);
		forallVariables.add(f1);

		SMTTerm assertion2 = left2.implies(right2);
		assertion2 = SMTTerm.forall(forallVariables, assertion2, null);


		//Assertion(s) 3 - normal field types

		SMTTerm assertion3 = SMTTerm.TRUE;

		for(String field : fieldSorts.keySet()){
			assertion3 = assertion3.and(addAssertionForField(field));
		}

		assertion3 = SMTTerm.forall(o, assertion3, null);

		//Assertion(s) 4 - array field types





		SMTTerm assertion4 = new SMTTerm.True();
		for(Sort s : thierarchy.getArraySortList()){
			String name = s.name().toString();
			addTypePredicate(s);
			String single = name.substring(0, name.length()-2);

			SMTFunction tp = getTypePredicate(name);

			if(tp == null){
				continue;
			}

			SMTTerm tpo = SMTTerm.call(tp, o);
			SMTTerm oNotNull = o.equal(nullConstant).not();
			SMTTerm premise = tpo.and(oNotNull);
			SMTTerm arr = SMTTerm.call(functions.get(ARR_FUNCTION_NAME),bi);
			SMTTerm selectArr = SMTTerm.call(selectFunction, h,o,arr);

			SMTTerm typeReq;
			if(single.equals("int") || single.equals("char") || single.equals("byte")){
				//System.err.println(name+" -> "+"Bounded Integer");
				typeReq = SMTTerm.call(getIsFunction(sorts.get(BINT_SORT)), selectArr);

			}
			else if(single.equals("java.lang.Object")){

				typeReq = SMTTerm.call(getIsFunction(sorts.get(OBJECT_SORT)), selectArr);
			}
			else if(single.equals("boolean")){

				typeReq = SMTTerm.call(getIsFunction(SMTSort.BOOL), selectArr);
			}
			else{
				//System.err.println(single);
				typeReq = SMTTerm.call(getIsFunction(sorts.get(OBJECT_SORT)), selectArr);

				Sort singleSort = services.getJavaInfo().getKeYJavaType(single).getSort();

				addTypePredicate(singleSort);
				SMTFunction tps = getTypePredicate(singleSort.name().toString());
				SMTTerm selectObjArr = castTermIfNecessary(selectArr, sorts.get(OBJECT_SORT));

				typeReq = typeReq.and(SMTTerm.call(tps,selectObjArr));

			}

			assertion4 = assertion4.and(premise.implies(typeReq));








		}

		List<SMTTermVariable> a4vars = new LinkedList<SMTTermVariable>();
		a4vars.add(o);
		a4vars.add(bi);

		assertion4 = SMTTerm.forall(a4vars, assertion4, null);


		//Combined Assertion

		SMTTerm finalAssertion = assertion1.and(assertion2).and(assertion3).and(assertion4);

		SMTFunctionDef wfdef = new SMTFunctionDef(wellformedFunction, h, finalAssertion);

		wellformedFunction = wfdef;
		functions.put(WELL_FORMED_NAME, wellformedFunction);
		functionDefinitionOrder.add(WELL_FORMED_NAME);

	}

	/**
	 * Create the created field constant. 
	 */
	private void createCreatedConstant() {
		SMTFunction c = new SMTFunction(CREATED_FIELD_NAME, new LinkedList<SMTSort>(), sorts.get(FIELD_SORT));
		functions.put(CREATED_FIELD_NAME, c);
	}

	/**
	 * Create assertion which states that a field is of the correct type.
	 * @param fieldName
	 * @return
	 */
	private SMTTerm addAssertionForField(String fieldName){
		SMTTerm f = SMTTerm.call(functions.get(fieldName));
		Sort type = fieldSorts.get(fieldName);

		SMTSort target = translateSort(type);

		SMTTermVariable h = new SMTTermVariable("h", sorts.get(HEAP_SORT));
		SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));

		List<SMTTerm> selectArgs = new LinkedList<SMTTerm>();
		selectArgs.add(h);
		selectArgs.add(o);
		selectArgs.add(f);
		//select(h,o,f)
		SMTTerm select = SMTTerm.call(selectFunction, selectArgs);
		//wellformed(h)


		SMTFunction isFunction = getIsFunction(target);
		//isTargetSort(select(h,o,f)) , TargetSort is bInt, object, bool, ...
		SMTTerm right = SMTTerm.call(isFunction,select);		

		if(target.getId().equals(OBJECT_SORT)){
			SMTTerm selectObj = castTermIfNecessary(select, target);
			String typeOfName = getTypePredicateName(type.toString()); 
			SMTFunction typeOf = typePredicates.get(typeOfName);
			if(typeOf == null){
				System.err.println(typeOfName);
			}
			SMTTerm typeOfTerm = SMTTerm.call(typeOf,selectObj);
			right = right.and(typeOfTerm);
		}

		SMTTerm assertionSub = right;

		//List<TermVariable> forallVars = new LinkedList<TermVariable>();

		//forallVars.add(h);
		//forallVars.add(o);

		//SMTTerm assertion = SMTTerm.forall(forallVars, assertionSub, null);

		return assertionSub;		

	}
	/**
	 * Casts a term to the specified sort, if the term is not already of that sort.
	 * @param term the term to be casted
	 * @param target the sort to which the term must be casted
	 * @return the casted term, or the original term if no cast was necessary
	 */
	private SMTTerm castTermIfNecessary(SMTTerm term, SMTSort target) {

		if (term.sort().getId().equals(target.getId())) {
			return term;
		} else {		

			SMTFunction cast = getCastFunction(term.sort(), target);
			return SMTTerm.call(cast, term);
		}
	}
	/**
	 * Return a function which casts a term from the source sort to the target sort.
	 * @param source
	 * @param target
	 * @return
	 */
	private SMTFunction getCastFunction(SMTSort source, SMTSort target) {
		SMTFunction f = functions.get(getCastFunctionName(source, target));
		if (f != null) {
			return f;
		} else {
			return createCastFunction(source, target);
		}
	}
	/**
	 * Returns the name of a cast function determined by the specified source and target sorts.
	 * @param source
	 * @param target
	 * @return
	 */
	private String getCastFunctionName(SMTSort source, SMTSort target) {
		return source.getId() + "2" + target.getId();
	}
	/**
	 * Creates a function which casts a term from the source sort tot the target sort.
	 * @param source
	 * @param target
	 * @return
	 */
	private SMTFunction createCastFunction(SMTSort source, SMTSort target) {
		String id = getCastFunctionName(source, target);

		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		domainSorts.add(source);
		SMTFunction f = new SMTFunction(id, domainSorts, target);

		functions.put(id, f);

		addCastAssertions(source, target, id);

		return f;

	}
	/**
	 * Adds the necessary assertions for a cast function
	 * @param source  source sort of the cast function
	 * @param target  target sort of the cast function
	 * @param id key where the cast function can be found in the function table
	 */
	private void addCastAssertions(SMTSort source, SMTSort target, String id) {

		SMTTermVariable v = new SMTTermVariable("v", source);
		SMTFunction fun = getCastFunction(source, target);
		SMTTerm call = SMTTerm.call(fun, v);
		long anySize = sorts.get(ANY_SORT).getBitSize();
		SMTTerm sub = null;
		if (target.getId().equals(sorts.get(ANY_SORT).getId())) {
			sub = call;
			if (source.equals(SMTSort.BOOL)) {
				sub = SMTTerm.ite(v, new SMTTermNumber(1, anySize,sorts.get(BINT_SORT)),
						new SMTTermNumber(0, anySize,sorts.get(BINT_SORT)));
			} else {
				SMTTermNumber n = sortNumbers.get(source);
				if(n==null){
					System.err.println(source.getId()+" has no number");
				}
				long bitDiff = anySize - source.getBitSize() - 3;
				if (bitDiff == 0) {
					sub = n.concat(v);
				} else {
					SMTTermNumber diff = new SMTTermNumber(0, bitDiff,sorts.get(BINT_SORT));
					sub = n.concat(diff.concat(v));
				}
			}

			SMTFunction is = functions.get(id);					
			SMTFunctionDef def = new SMTFunctionDef(is, v, sub);
			functions.put(id, def);
			functionDefinitionOrder.add(id);
			return;			


		} else if (source.getId().equals(sorts.get(ANY_SORT).getId())) {

			if (target.equals(SMTSort.BOOL)) {
				SMTTermNumber one = new SMTTermNumber(1, anySize,sorts.get(BINT_SORT));
				SMTTermNumber zero = new SMTTermNumber(0, anySize,sorts.get(BINT_SORT));

				SMTTerm implies1 = v.equal(one).implies(
						call.equal(SMTTerm.TRUE));
				SMTTerm implies2 = v.equal(zero).implies(
						call.equal(SMTTerm.FALSE));

				sub = implies1.and(implies2);

			} else {
				// extract type
				long targetSize = target.getBitSize();
				long firstBit = anySize - 1;
				long lastBit = anySize - 3;

				List<SMTSort> extrIDDomain = new LinkedList<SMTSort>();
				extrIDDomain.add(sorts.get(ANY_SORT));

				SMTFunction isFunction = getIsFunction(target);
				SMTTerm isCall = SMTTerm.call(isFunction,v);

				SMTTerm left = isCall;

				// extract value

				firstBit = targetSize - 1;
				lastBit = 0;

				String extractValID = "(_ extract " + firstBit + " " + lastBit
						+ ")";
				List<SMTSort> extrValDomain = new LinkedList<SMTSort>();
				extrValDomain.add(sorts.get(ANY_SORT));
				SMTFunction extractVal = new SMTFunction(extractValID,
						extrIDDomain, SMTSort.mkBV(targetSize));

				SMTTerm extractValue = SMTTerm.call(extractVal, v);

				SMTTerm right = call.equal(extractValue);


				if(target.getId().equals(OBJECT_SORT)){
					SMTTerm condition = left;
					SMTTerm trueCase = extractValue;
					SMTTerm falseCase = nullConstant;
					sub = new SMTTermITE(condition, trueCase, falseCase);					
					SMTFunction is = functions.get(id);					
					SMTFunctionDef def = new SMTFunctionDef(is, v, sub);
					functions.put(id, def);
					functionDefinitionOrder.add(id);
					return;

				}
				else if(target.getId().equals(LOCSET_SORT)){
					SMTTerm condition = left;
					SMTTerm trueCase = extractValue;
					SMTTerm falseCase = emptyConstant;
					sub = new SMTTermITE(condition, trueCase, falseCase);					
					SMTFunction is = functions.get(id);					
					SMTFunctionDef def = new SMTFunctionDef(is, v, sub);
					functions.put(id, def);
					functionDefinitionOrder.add(id);
					return;
				}
				else{
					sub = left.implies(right);
				}



			}

		}
		else{
			SMTSort any = sorts.get(ANY_SORT);

			String sourceName = source.getId();
			String targetName =target.getId();

			if(sourceName.equals(FIELD_SORT) || sourceName.equals(HEAP_SORT) || targetName.equals(FIELD_SORT) || targetName.equals(HEAP_SORT)){

				throw new RuntimeException("Error: Attempted cast between "+sourceName+ " to "+targetName);

			}

			SMTFunction s2any = getCastFunction(source, any);
			SMTFunction any2t = getCastFunction(any,target);

			SMTTerm body = SMTTerm.call(s2any,v);
			body = SMTTerm.call(any2t,body);

			SMTFunctionDef def = new SMTFunctionDef(functions.get(id), v, body);
			functions.put(id, def);
			functionDefinitionOrder.add(id);
			return;





		}
		if (sub != null) {
			SMTTerm assertion = SMTTerm.forall(v, sub, null);
			assertion.setComment("Assertion for "+fun.getId());
			castAssertions.add(assertion);
		}

	}
	/**
	 * Recursively finds all sorts in a term
	 * @param sorts list of accumulated sorts
	 * @param term the term where we look for the sorts
	 */
	private void findSorts(Set<Sort> sorts, Term term){

		Sort s = term.sort();

		JavaInfo javaInfo = services.getJavaInfo();

		Sort object = javaInfo.getJavaLangObject().getSort();
		Sort nullSort = services.getTypeConverter().getHeapLDT().getNull().sort();
		if(s.extendsTrans(object) && !s.equals(nullSort))  {

			sorts.add(s);		

		}




		for(Term sub : term.subs()){
			findSorts(sorts, sub);
		}

	}

	/**
	 * Translates a KeY problem into a SMTFile.
	 * 
	 * @param problem
	 *            The KeY proof obligation.
	 * @return
	 */
	public SMTFile translateProblem(Term problem) {

		SMTFile file = new SMTFile();

		//initialize smt sorts

		cc.countConstants(problem);		
		initSMTSorts();

		findSorts(javaSorts, problem);

		//create special functions and constants
		createSpecialFunctions();


		// Translate the proof obligation
		SMTTerm po = translateTerm(problem);
		po = po.not();




		po.setComment("The negated proof obligation");

		generateTypeConstraints();		
		generateFieldFunctionDefinitions();
		generateWellFormedAssertions();
		generateLengthAssertions();

		//generateClassInvariantDefinition();

		if(guardOverflow){

			OverflowChecker oc = new OverflowChecker(sorts.get(BINT_SORT));
			Set<SMTTerm> groundTerms = new HashSet<SMTTerm>();
			oc.searchArithGroundTerms(groundTerms, po);
			overflowGuards.addAll(oc.createGuards(groundTerms));			

			oc.processTerm(po);


		}







		// Translate the selected taclets.
		// translateTaclets();
		// Instantiate the any type with the other types.
		// instantiateTaletAssertions();

		// Add SMT sorts to file.
		for (String s : sorts.keySet()) {
			file.addSort(sorts.get(s));
		}

		// Add type predicates as functions to KeY file.
		for (String s : typePredicates.keySet()) {
			file.addFunction(typePredicates.get(s));
		}

		// Add other function declarations to file.
		for (String s : functions.keySet()) {
			//System.err.println("Found: "+functions.get(s));
			SMTFunction f = functions.get(s);
			if( !(f instanceof SMTFunctionDef)){
				file.addFunction(functions.get(s));
			}

		}
		// Add function definitions to file.
		for(String s : functionDefinitionOrder){
			file.addFunction(functions.get(s));
		}

		// Add assertions for type hierarchy to file.
		for (String s : typeAssertions.keySet()) {
			file.addFormula(typeAssertions.get(s));
		}

		// Add function return type assertions to file.
		file.addFormulas(functionTypeAssertions);
		// Add cast assertions to file.
		file.addFormulas(castAssertions);
		// Add wellformedness assertions to file.
		file.addFormulas(wellFormedAssertions);

		// Add overflow formulas to file

		for(SMTTerm term : overflowGuards){
			term.setComment("Overflow guard");
			file.addFormula(term);
		}
		//should all objects satisfy their invariant?
		if(settings.invarianForall()){
			SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));
			SMTTermVariable h = new SMTTermVariable("h", sorts.get(HEAP_SORT));
			List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
			vars.add(h);
			vars.add(o);			
			SMTTerm inv = SMTTerm.call(functions.get(CLASS_INVARIANT), h,o);
			SMTTerm forall = inv.forall(vars);
			file.addFormula(forall);
		}

		// Add assertions resulting from taclets to file.
		// file.addFormulas(tacletAssertions);

		// Add assertions stating that each type has at least an instance to
		// file.
		// generateExistenceAssertions();
		// file.addFormulas(existenceAssertions);

		// Add assertion stating that all fields are distinct to file.


		// Add the proof obligation to file.
		file.addFormula(po);

		return file;
	}



	/**
	 * Translates a KeY term to an SMT term.
	 * 
	 * @param term
	 *            the KeY term.
	 * @return the SMT term.
	 */
	public SMTTerm translateTerm(Term term) {

		// System.err.println("Translate: "+term);

		Operator op = term.op();

		if (opTable.containsKey(op)) {
			SMTTerm left = translateTerm(term.sub(0));
			SMTTerm right = translateTerm(term.sub(1));

			//make necessary casts

			if(!left.sort().getId().equals(right.sort().getId())){

				if(left.sort().getId().equals(ANY_SORT)){

					if(right instanceof SMTTermCall){
						SMTTermCall tc = (SMTTermCall) right;
						if(tc.getFunc().getId().startsWith(ANY_SORT+"2")){
							right = tc.getArgs().get(0);
						}
						else{
							right = castTermIfNecessary(right, sorts.get(ANY_SORT));
						}
					}
					else{
						right = castTermIfNecessary(right, sorts.get(ANY_SORT));
					}



				}
				else if(right.sort().getId().equals(ANY_SORT)){
					if(left instanceof SMTTermCall){
						SMTTermCall tc = (SMTTermCall) left;
						if(tc.getFunc().getId().startsWith(ANY_SORT+"2")){
							left = tc.getArgs().get(0);;
						}
						else{
							left = castTermIfNecessary(left, sorts.get(ANY_SORT));
						}
					}
					else{
						left = castTermIfNecessary(left, sorts.get(ANY_SORT));
					}
				}




			}




			return left.multOp(opTable.get(op), right);
		} else if (op == Junctor.NOT) {
			SMTTerm sub = translateTerm(term.sub(0));
			return sub.not();
		} else if (op == IfThenElse.IF_THEN_ELSE) {

			SMTTerm condition = translateTerm(term.sub(0));
			SMTTerm trueCase = translateTerm(term.sub(1));
			SMTTerm falseCase = translateTerm(term.sub(2));

			if(!trueCase.sort().getId().equals(falseCase.sort().getId())){
				trueCase = castTermIfNecessary(trueCase, sorts.get(ANY_SORT));
				falseCase = castTermIfNecessary(falseCase, sorts.get(ANY_SORT));
			}

			return SMTTerm.ite(condition, trueCase, falseCase);

		} else if (op == Quantifier.ALL) {
			ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
			Debug.assertTrue(vars.size() == 1);

			SMTTermVariable var = translateVariable(vars.get(0));
			List<SMTTermVariable> variables = new LinkedList<SMTTermVariable>();
			quantifiedVariables.add(var);

			variables.add(var);

			String sortName = vars.get(0).sort().name()
					.toString();

			String id = getTypePredicateName(sortName);

			SMTTerm sub = translateTerm(term.sub(0));

			if (typePredicates.containsKey(id) && !sortName.equals("java.lang.Object")) {
				SMTTerm call = SMTTerm.call(typePredicates.get(id), var);
				sub = call.implies(sub);
			}
			SMTTerm result = SMTTerm.forall(variables, sub, null);
			quantifiedVariables.remove(quantifiedVariables.size() - 1);
			return result;

		} else if (op == Quantifier.EX) {
			ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
			Debug.assertTrue(vars.size() == 1);

			SMTTermVariable var = translateVariable(vars.get(0));
			List<SMTTermVariable> variables = new LinkedList<SMTTermVariable>();

			quantifiedVariables.add(var);

			variables.add(var);
			String sortName = vars.get(0).sort().name()
					.toString();

			String id = getTypePredicateName(sortName);

			SMTTerm sub = translateTerm(term.sub(0));

			if (typePredicates.containsKey(id) && !sortName.equals("java.lang.Object")) {
				SMTTerm call = SMTTerm.call(typePredicates.get(id), var);
				sub = call.and(sub);
			}
			SMTTerm result = SMTTerm.exists(variables, sub, null);
			quantifiedVariables.remove(quantifiedVariables.size() - 1);
			return result;

		} else if (op == Junctor.TRUE) {
			return SMTTerm.TRUE;
		} else if (op == Junctor.FALSE) {
			return SMTTerm.FALSE;
		} else if (op == services.getTypeConverter().getHeapLDT().getNull()) {
			return nullConstant;
		} else if (op instanceof QuantifiableVariable) {

			// translate as variable or constant
			QuantifiableVariable qop = (QuantifiableVariable) op;
			SMTTermVariable var = translateVariable((QuantifiableVariable) op);

			if (quantifiedVariables.contains(var)) {
				return var;
			} else {
				// System.err.println("Create constant: "+var);
				SMTFunction constant = translateConstant(var.getId(),
						qop.sort());
				return SMTTerm.call(constant);
			}
		} else if (op instanceof ProgramVariable) {
			ProgramVariable pv = (ProgramVariable) op;

			SMTFunction constant = translateConstant(pv.name().toString(),
					pv.sort());
			return SMTTerm.call(constant);
		} else if (op == services.getTypeConverter().getIntegerLDT()
				.getNumberSymbol()) {
			Debug.assertTrue(term.arity() == 1);
			long num = NumberTranslation.translate(term.sub(0)).longValue();
			long size = sorts.get(BINT_SORT).getBitSize();
			long bound = sorts.get(BINT_SORT).getBound();
			//modulo max int
			num = num % bound;
			if (num < 0) {
				SMTTerm zero = new SMTTermNumber(0, size, sorts.get(BINT_SORT));
				SMTTerm n = new SMTTermNumber(-num, size,sorts.get(BINT_SORT));
				return zero.minus(n);
			}
			return new SMTTermNumber(num, size,sorts.get(BINT_SORT));

		} else if (op instanceof Function) {
			Function fun = (Function) op;

			if (isTrueConstant(fun, services)) {
				return SMTTerm.TRUE;
			} else if (isFalseConstant(fun, services)) {
				return SMTTerm.FALSE;
			} else if (fun == services.getTypeConverter().getIntegerLDT()
					.getNeg()) {
				SMTTerm left = new SMTTermNumber(0, settings.getIntBound(),sorts.get(BINT_SORT));
				SMTTerm right = translateTerm(term.sub(0));
				return left.minus(right);
			} else {
				return translateCall(fun, term.subs());
			}
		} else {
			String msg = "Unable to translate " + term + " of type "
					+ term.getClass().getName();
			throw new RuntimeException(msg);
		}
	}
	/**
	 * Translates a quantified variable.
	 * @param q
	 * @return
	 */
	private SMTTermVariable translateVariable(QuantifiableVariable q) {
		SMTSort s = translateSort(q.sort());
		SMTTermVariable var = new SMTTermVariable(q.name().toString(), s);
		return var;
	}

	//	/**
	//	 * @deprecated
	//	 */
	//	private void translateTaclets() {
	//		Collection<Taclet> taclets = settings.getTaclets();
	//		if (!settings.makesUseOfTaclets() || taclets == null
	//				|| taclets.isEmpty()) {
	//			return;
	//		}
	//		TacletSetTranslation tacletSetTranslation = new DefaultTacletSetTranslation(
	//				services, settings);
	//
	//		for (TacletFormula tf : tacletSetTranslation.getTranslation(javaSorts)) {
	//			for (Term tacletTerm : tf.getInstantiations()) {
	//				tacletAssertions.add(translateTerm(tacletTerm));
	//			}
	//		}
	//	}
	/**
	 * Translates a KeY sort to an SMT sort.
	 * @param s
	 * @return
	 */
	private SMTSort translateSort(Sort s) {

		if (s.equals(boolSort)) {
			return SMTSort.BOOL;
		} else if (s.equals(Sort.FORMULA)) {
			return SMTSort.BOOL;
		} else if (s.equals(integerSort)) {
			return sorts.get(BINT_SORT);
		} else if (s.equals(heapSort)) {
			return sorts.get(HEAP_SORT);
		} else if (s.equals(fieldSort)) {
			return sorts.get(FIELD_SORT);
		} else if (s.equals(locsetSort)) {
			return sorts.get(LOCSET_SORT);
		} else if (s.equals(Sort.ANY)) {
			return sorts.get(ANY_SORT);
		} else if(s.equals(seqSort)){
			return sorts.get(SEQ_SORT);
		}		
		else {

			Sort obj = services.getJavaInfo().getJavaLangObject().getSort();

			if(!(s.equals(obj)|| s.extendsTrans(obj))){
				throw new RuntimeException("Translation Failed: Unsupported Sort: "+s.name());
			}

			//System.out.println("Found sort in PO: "+s);
			javaSorts.add(s);
			addTypePredicate(s);
			// addTypeConstarints(s);
			return sorts.get(OBJECT_SORT);
		}
	}
	/**
	 * Generates the necessary assertions for specifying the type hierarchy.
	 */
	private void generateTypeConstraints() {
		//create type hierarchy assertions
		Set<Sort> tempsorts = new HashSet<Sort>();
		tempsorts.addAll(javaSorts);		
		for (Sort s : tempsorts) {
			addTypeConstarints(s);
		}

		//null is of all types
		List<SMTTerm> typeCalls = new LinkedList<SMTTerm>();
		for(String s : typePredicates.keySet()){
			SMTFunction f = typePredicates.get(s);
			typeCalls.add(SMTTerm.call(f,nullConstant));
		}
		SMTTerm nullTypeAssertion = SMTTerm.and(typeCalls);
		nullTypeAssertion.setComment("Assert that null is all types");
		typeAssertions.put("null", nullTypeAssertion);

		//create exactinstance predicate for all used types
		Set<Sort> tempSortList = new HashSet<Sort>();
		tempSortList.addAll(extendedJavaSorts);
		for(Sort s : tempSortList){
			getExactInstanceFunction(s);
		}
		extendedJavaSorts = tempSortList;
	}

	/**
	 * Generates the type assertions for the java reference type s.
	 * @param s
	 */
	private void addTypeConstarints(Sort s) {
		// Did we already specify the constraints?
		if (typeAssertions.containsKey(s.toString())) {
			return;
		}
		// Do not specify constraint for these sorts:
		if (s == Sort.ANY || s.name().toString().equals("java.lang.Object")
				|| s.name().toString().equalsIgnoreCase("Null")) {
			return;
		}

		/*
		 * First we need to say that if an object is of type s, then it is
		 * of the type of its parents as well.
		 */

		//create a variable x of type object
		SMTTermVariable var = new SMTTermVariable("x", sorts.get(OBJECT_SORT));
		//generate the type predicate for sort s
		addTypePredicate(s);
		//get the parent of sort s
		Set<SortNode> parents = thierarchy.getParents(s);
		SMTTerm parentsFormulae = SMTTerm.TRUE;
		//for each parent sort of s
		for (SortNode n : parents) {
			//first we need to generate the type constraints for the parent
			addTypeConstarints(n.getSort());			
			//we should have a type predicate for the parent now
			SMTFunction typefun = typePredicates.get(getTypePredicateName(n
					.getSort().toString()));
			//no type predicate means that the parent was Object or Any, so ignore it
			if (typefun == null)
				continue;
			//say that x is of parent type
			SMTTerm parType = SMTTerm.call(typefun, var);
			//add it to the other parent assertions
			parentsFormulae = parentsFormulae.and(parType);
		}

		// typeOfS(x)
		SMTFunction tf = typePredicates.get(getTypePredicateName(s.toString()));
		if (tf == null) {
			System.err.println("Error: could not find type predicate: "
					+ getTypePredicateName(s.toString()));
		}
		SMTTerm left = SMTTerm.call(tf, var);
		SMTTerm right = null;
		// x == null
		List<SMTTerm> eqnullArgs = var.toList();
		eqnullArgs.add(SMTTerm.call(functions.get(NULL_CONSTANT)));
		SMTTerm eqnull = SMTTerm.equal(eqnullArgs);

		SMTTerm eiCall = null;		
		if (s.isAbstract()) {


			SMTFunction ei = getExactInstanceFunction(s);			
			eiCall = SMTTerm.call(ei,var);		

			//equals null or (is parent and not exact instance)
			right = eqnull.or(parentsFormulae.and(eiCall.not()));

		}

		if(!isInterface(s)){
			Sort concreteParent = null;
			Set<SortNode> concreteParents = concreteHierarchy.getParents(s);

			for (SortNode n : concreteParents) {
				addTypePredicate(n.getSort());
				if (concreteParent == null
						|| concreteParent.toString().equals("java.lang.Object")) {
					concreteParent = n.getSort();
				}

			}
			// System.err.println("Concrete parent: " + concreteParent);
			if (concreteParent == null) {
				System.err.println(s + " has no concrete Parent");
			}

			Set<SortNode> siblings = concreteHierarchy
					.getChildren(concreteParent);
			SMTTerm sibFormulae = SMTTerm.FALSE;
			// System.err.println("Processing siblings:");
			for (SortNode sibling : siblings) {
				// System.err.println("Check: "+sibling);
				if (sibling.getSort().equals(s)) {
					continue;
				}

				addTypePredicate(sibling.getSort());
				SMTFunction typefun = typePredicates
						.get(getTypePredicateName(sibling.getSort().toString()));
				if (typefun == null)
					continue;

				SMTTerm sibType = SMTTerm.call(typefun, var);
				sibFormulae = sibFormulae.or(sibType);
			}
			if(!s.isAbstract()){
				right = eqnull.or(parentsFormulae.and(sibFormulae.not()));
			}
			else{
				right = eqnull.or(parentsFormulae.and(eiCall.not().and(sibFormulae.not())));
			}


		}

		SMTTerm forall = SMTTerm.forall(var, left.implies(right), null);

		forall.setComment("Assertions for type "+s.name());

		typeAssertions.put(s.name().toString(), forall);

	}

	private String varName(char c) {
		varNr++;
		return c+"_" + varNr;
	}
	/**
	 * Generates an assertion which states that the function f is of type specified by the type predicate tp.
	 * @param f
	 * @param tp
	 */
	private void addTypeAssertion(SMTFunction f, SMTFunction tp) {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		List<SMTTerm> args = new LinkedList<SMTTerm>();
		for (SMTSort s : f.getDomainSorts()) {
			SMTTermVariable v = new SMTTermVariable(varName('x'), s);

			vars.add(v);
			args.add(v);

		}
		SMTTerm fcall = SMTTerm.call(f, args);
		SMTTerm tpcall = SMTTerm.call(tp, fcall);
		SMTTerm asrt = SMTTerm.forall(vars, tpcall, null);
		if (!functionTypeAssertions.contains(asrt)) {
			asrt.setComment("Assertion regarding the type of "+f.getId());
			functionTypeAssertions.add(asrt);			
		}
	}
	/**
	 * 
	 * @param sortName
	 * @return the type predicate corresponding to the given sort name
	 */
	private SMTFunction getTypePredicate(String sortName) {
		return typePredicates.get(getTypePredicateName(sortName));
	}

	public static String getTypePredicateName(String id) {
		return "typeof_" + id;
	}
	/**
	 * 
	 * @param s
	 * @return true if s or a subtype of s appears in the proof obligation
	 */
	private boolean appearsInPO(Sort s){


		for(Sort poSort : javaSorts){

			if(poSort.extendsTrans(s)){
				return true;
			}



		}

		return false;



	}
	/**
	 * Creates a type predicate for the sort s if acceptable.
	 * @param s
	 */
	private void addTypePredicate(Sort s) {

		if(!appearsInPO(s)){
			return;
		}

		String id = s.name().toString();
		String name = getTypePredicateName(id);
		if (!typePredicates.containsKey(name)) {
			SMTSort imageSort = SMTSort.BOOL;
			SMTSort domainSort = sorts.get(OBJECT_SORT);
			List<SMTSort> domainSorts = new LinkedList<SMTSort>();
			domainSorts.add(domainSort);
			SMTFunction fun = new SMTFunction(name, domainSorts, imageSort);

			if(id.equals("java.lang.Object")){
				fun = new SMTFunctionDef(fun, new SMTTermVariable("o", sorts.get(OBJECT_SORT)), SMTTerm.TRUE);
			}
			else{
				extendedJavaSorts.add(s);
			}

			typePredicates.put(name, fun);

		}
	}

	/**
	 * Creates an SMT constant with the specified id and sort.
	 * @param id
	 * @param s
	 * @return
	 */
	private SMTFunction translateConstant(String id, Sort s) {

		if (functions.containsKey(id)) {
			return functions.get(id);
		}
		SMTSort imageSort = translateSort(s);
		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		SMTFunction fun = new SMTFunction(id, domainSorts, imageSort);
		functions.put(id, fun);
		SMTFunction tp = getTypePredicate(s.name().toString());
		if (tp != null) {
			addTypeAssertion(fun, tp);
		}

		types.putConstantType(Util.processName(id), imageSort);
		types.putOriginalConstantType(Util.processName(id), s);
		return fun;

	}


	/**
	 * Translates a function call of function f with argument subs.
	 * @param fun
	 * @param subs
	 * @return
	 */
	private SMTTerm translateCall(Function fun, ImmutableArray<Term> subs) {

		String name = fun.name().toString();

		//handle sort constants
		if (fun.sort().equals(fieldSort) && subs.isEmpty()) {
			name = name.replace("$", "");
			JavaInfo info = services.getJavaInfo();
			Sort sort = info.getAttribute(name).getKeYJavaType().getSort();

			fieldSorts.put(name, sort);
			types.putFieldType(Util.processName(name), translateSort(sort));
			types.putConstantType(Util.processName(name), sorts.get(FIELD_SORT));

		}
		else if(subs.isEmpty()){
			types.putConstantType(Util.processName(name) , translateSort(fun.sort()));
		}

		// handle select functions
		if (name.endsWith(SELECT)) {
			SMTSort target = translateSort(fun.sort());
			SMTTerm selectCall = call(selectFunction, subs);
			SMTTerm result = castTermIfNecessary(selectCall, target);
			if(target.getId().equals(OBJECT_SORT) && !fun.sort().name().toString().equals("java.lang.Object")){
				Sort castTarget = fun.sort();

				SMTFunction f = getCastFunction(castTarget);				
				result = SMTTerm.call(f,result);

			}




			return result;
		}
		//handle seqGet functions
		if(name.endsWith(SEQ_GET)){

			SMTSort target = translateSort(fun.sort());
			SMTTerm seqGetCall = call(functions.get(SEQ_GET), subs);
			SMTTerm result = castTermIfNecessary(seqGetCall, target);
			if(target.getId().equals(OBJECT_SORT) && !fun.sort().name().toString().equals("java.lang.Object")){
				Sort castTarget = fun.sort();

				SMTFunction f = getCastFunction(castTarget);				
				result = SMTTerm.call(f,result);

			}

			return result;

		}

		SMTFunction function;
		if (functions.containsKey(name)) {
			function = functions.get(name);
		}
		else if(name.equals(WELL_FORMED_NAME)){
			function = wellformedFunction;
		}
		else if(name.equals(ELEMENTOF)){
			function = elementOfFunction;
		}
		else if(name.endsWith("::exactInstance")){
			SortDependingFunction sdf = (SortDependingFunction) fun;
			function = getExactInstanceFunction(sdf.getSortDependingOn());
		}
		else if(name.endsWith("::instance")){
			SortDependingFunction sdf = (SortDependingFunction) fun;

			addTypePredicate(sdf.getSortDependingOn());

			function = getTypePredicate(sdf.getSortDependingOn().name().toString());



		}
		else if(name.endsWith("::cast")){
			SortDependingFunction sdf = (SortDependingFunction) fun;


			SMTSort target = translateSort(sdf.getSortDependingOn());

			if(target.getId().equals(OBJECT_SORT)){
				function = getCastFunction(sdf.getSortDependingOn());
			}
			else{

				Sort s = subs.get(0).sort();
				SMTSort source = translateSort(s);

				//if already the correct type ignore the cast
				if(source.getId().equals(target.getId())){
					return translateTerm(subs.get(0));
				}

				function = getCastFunction(source, target);



			}



		}
		else if(name.endsWith("::<inv>")){
			if(functions.containsKey(CLASS_INVARIANT)){
				function =  functions.get(CLASS_INVARIANT);
			}
			else{
				function = createClassInvariantFunction();
			}						
		}
		else {
			List<SMTSort> domainSorts = new LinkedList<SMTSort>();

			for (int i = 0; i < fun.argSorts().size(); ++i) {
				Sort s = fun.argSort(i);
				domainSorts.add(translateSort(s));
			}

			SMTSort imageSort = translateSort(fun.sort());

			function = new SMTFunction(name, domainSorts, imageSort);
			functions.put(name, function);

			// add type assertion if necessary
			SMTFunction tp = getTypePredicate(fun.sort().name().toString());
			if (tp != null) {
				addTypeAssertion(function, tp);
			}
		}

		if(function == null){
			System.err.println("Null function "+name);
		}





		return call(function, subs);

	}

	/**
	 * Creates the class invariant function.
	 * @return
	 */
	private SMTFunction createClassInvariantFunction() {
		SMTFunction function;
		String id = CLASS_INVARIANT;			
		List<SMTSort> domain = new LinkedList<SMTSort>();
		domain.add(sorts.get(HEAP_SORT));
		domain.add(sorts.get(OBJECT_SORT));			
		function = new SMTFunction(id,domain,SMTSort.BOOL);
		functions.put(CLASS_INVARIANT, function);
		return function;
	}

	/**
	 * Creates a reference type cast function for the castTarget type.
	 * @param castTarget
	 * @return
	 */
	private SMTFunction getCastFunction(Sort castTarget) {

		SMTSort sort = translateSort(castTarget);

		if(sort.getId().equals(OBJECT_SORT)){
			SMTFunction f;
			String castFunctionName = getCastFunctionName(castTarget);
			if(functions.containsKey(castFunctionName)){
				f = functions.get(castFunctionName);
			}
			else{
				List<SMTSort> domain = new LinkedList<SMTSort>();
				domain.add(sorts.get(OBJECT_SORT));

				SMTSort image = sorts.get(OBJECT_SORT);

				f = new SMTFunction(castFunctionName, domain, image);
				functions.put(castFunctionName, f);

				addCastFunctionAssertions(castTarget);


			}
			return f;
		}
		else{
			return getCastFunction(sorts.get(OBJECT_SORT), sort);
		}




	}


	/**
	 * Adds the necessary assertions for the cast function for the castTarget sort. 
	 * @param castTarget
	 */
	private void addCastFunctionAssertions(Sort castTarget) {
		addTypePredicate(castTarget);
		SMTFunction f = functions.get(getCastFunctionName(castTarget));
		SMTFunction t = getTypePredicate(castTarget.name().toString());

		if(t == null){
			System.err.println("No tp for "+castTarget.name());
		}

		SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));
		//cast(o)
		SMTTerm fo = SMTTerm.call(f,o);
		SMTTerm.call(t,fo);
		//typeof(o)
		SMTTerm to = SMTTerm.call(t,o);


		SMTTerm body = SMTTerm.ite(to, o, nullConstant);
		SMTTerm assertion = fo.equal(body);



		assertion = SMTTerm.forall(o, assertion, null);

		assertion.setComment("Assertion for "+castTarget+" cast function.");

		typeAssertions.put(f.getId(), assertion);



	}



	private String getCastFunctionName(Sort castTarget) {
		return "cast"+castTarget;
	}
	/**
	 * Creates the exactInstance predicate for a sort s.
	 * @param s
	 * @return
	 */
	private SMTFunction getExactInstanceFunction(Sort s){

		SMTSort smtSort = translateSort(s);

		if(!smtSort.getId().equals(OBJECT_SORT)){	

			System.err.println(s.name() + "is not an object");

			return getIsFunction(smtSort);			
		}		
		else if(functions.containsKey(getExactInstanceName(s.name().toString()))){
			return functions.get(getExactInstanceName(s.name().toString()));			
		}
		else{
			SMTFunction f = createExactInstanceDefinition(s);
			functions.put(getExactInstanceName(s.name().toString()), f);
			if(f instanceof SMTFunctionDef){
				functionDefinitionOrder.add(getExactInstanceName(s.name().toString()));
			}
			return f;
		}


	}

	public static String getExactInstanceName(String sortName){
		return "exactInstanceOf_"+sortName;
	}

	/**
	 * 
	 * @param s
	 * @return true if s is an interface
	 */
	private boolean isInterface(Sort s){
		KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(s);

		if(kjt == null){
			return false;
		}

		return kjt.getJavaType() instanceof InterfaceDeclaration;

	}
	/**
	 * Creates the exactInstance function assertion(definition for final classes) for sort s.
	 * @param sort
	 * @return
	 */
	private SMTFunction createExactInstanceDefinition(Sort sort){
		//System.out.println("EI: "+sort);
		String id = getExactInstanceName(sort.name().toString());
		SMTSort image = SMTSort.BOOL;
		SMTTermVariable o = new SMTTermVariable("o", sorts.get(OBJECT_SORT));

		addTypePredicate(sort);

		SMTFunction typeofFun = getTypePredicate(sort.name().toString());
		SMTTerm typeof;
		if(typeofFun !=null){
			typeof = SMTTerm.call(typeofFun,o);
		}
		else{
			typeof = SMTTerm.TRUE;
		}

		SMTTerm children = o.equal(nullConstant);

		for(SortNode node : thierarchy.getChildren(sort)){
			Sort child = node.getSort();

			addTypePredicate(child);
			SMTFunction typeofChildFun = getTypePredicate(child.name().toString());
			if(typeofChildFun == null){
				continue;
			}

			SMTTerm typeofChild = SMTTerm.call(typeofChildFun,o);
			children = children.or(typeofChild);
		}

		for(Sort s : thierarchy.getSortList()){

			if(s.equals(sort) || sort.extendsTrans(s)){
				continue;
			}



			if(isInterface(s)){
				addTypePredicate(s);
				SMTFunction typeOfI = getTypePredicate(s.name().toString());
				if(typeOfI == null){
					continue;
				}
				//System.out.println("Add: "+s);
				SMTTerm call = SMTTerm.call(typeOfI, o);
				children = children.or(call);


			}


		}

		children = children.not();			
		KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);

		boolean finalClass =  kjt!=null&&kjt.getJavaType() instanceof ClassDeclaration
				&& ((ClassDeclaration) kjt.getJavaType()).isFinal();


		if(kjt!=null && kjt.getJavaType() instanceof ArrayDeclaration){
			finalClass = true;
		}



		SMTTerm body = typeof.and(children);

		if(finalClass){
			SMTFunctionDef def = new SMTFunctionDef(id, o, image, body);
			def.setComment("exactInstance function definition for "+sort.name());
			return def;
		}
		else{




			List<SMTSort> domain = new LinkedList<SMTSort>();
			domain.add(sorts.get(OBJECT_SORT));
			SMTFunction fun = new SMTFunction(id, domain, image);

			SMTTerm call = SMTTerm.call(fun,o);
			body = call.implies(body);
			body = body.forall(o);

			body.setComment("Assertion for exactInstance for sort: "+sort.name());

			typeAssertions.put(id, body);

			return fun;			
		}






	}

	/**
	 * Creates a function for checking if the given sort is the actual sort of an Any value.
	 * @param sort
	 * @return
	 */
	private SMTFunction getIsFunction(SMTSort sort){
		String id = "is"+sort.getId();
		if(functions.containsKey(id)){
			return functions.get(id);
		}

		List<SMTSort> domain = new LinkedList<SMTSort>();
		domain.add(sorts.get(ANY_SORT));
		SMTSort image = SMTSort.BOOL;

		SMTFunction isFunction = new SMTFunction(id, domain, image);
		SMTFunctionDef def;

		SMTTermVariable v = new SMTTermVariable("x", sorts.get(ANY_SORT));
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.add(v);
		long anySize = sorts.get(ANY_SORT).getBitSize();

		//special case for boolean
		if(sort.equals(SMTSort.BOOL)){

			SMTTermNumber zero = new SMTTermNumber(0, anySize,sorts.get(BINT_SORT));
			SMTTermNumber one = new SMTTermNumber(1, anySize,sorts.get(BINT_SORT));
			// x = 1 or x = 0
			SMTTerm t = v.equal(one).or(v.equal(zero));

			def = new SMTFunctionDef(isFunction, vars, t);


			functions.put(id, def);
			functionDefinitionOrder.add(id);
			return def;			
		}




		SMTTermNumber targetNumber = sortNumbers.get(sort);

		long firstBit = anySize - 1;
		long lastBit = anySize - 3;

		String extractTypeID = "(_ extract " + firstBit + " " + lastBit + ")";
		List<SMTSort> extrIDDomain = new LinkedList<SMTSort>();
		extrIDDomain.add(sorts.get(ANY_SORT));

		SMTFunction extractId = new SMTFunction(extractTypeID, extrIDDomain,
				SMTSort.mkBV(3));	

		SMTTerm extract = SMTTerm.call(extractId, v);

		SMTTerm isAssertion = extract.equal(targetNumber);

		def = new SMTFunctionDef(isFunction, vars, isAssertion);

		functions.put(id, def);
		functionDefinitionOrder.add(id);
		return def;




	}
	/**
	 * Creates an SMTTermCall using the given function and arguments.
	 * @param function
	 * @param subs
	 * @return
	 */
	private SMTTerm call(SMTFunction function, ImmutableArray<Term> subs) {
		List<SMTTerm> subTerms = new LinkedList<SMTTerm>();
		int i = 0;
		for (Term t : subs) {
			SMTTerm sub = translateTerm(t);
			SMTSort target = function.getDomainSorts().get(i);

			sub = castTermIfNecessary(sub, target);
			subTerms.add(sub);
			i++;
		}
		return SMTTerm.call(function, subTerms);
	}

	private boolean isTrueConstant(Operator o, Services s) {
		return o.equals(s.getTypeConverter().getBooleanLDT().getTrueConst());
	}

	private boolean isFalseConstant(Operator o, Services s) {
		return o.equals(s.getTypeConverter().getBooleanLDT().getFalseConst());
	}

	@Override
	public Collection<Throwable> getExceptionsOfTacletTranslation() {		
		return new LinkedList<Throwable>();
	}

	/**
	 * Class for counting constants of different types appearing in the proof obligation.
	 * @author mihai
	 *
	 */
	public class ConstantCounter{

		Set<String> locsets;

		Set<String> heaps;

		Set<String> fields;

		public ConstantCounter(){
			locsets = new HashSet<String>();
			heaps = new HashSet<String>();
			fields = new HashSet<String>();
		}

		public void countConstants(Term t){

			if(t.subs().size() == 0){

				Sort s = t.sort();
				String str = t.toString();
				if(s.equals(heapSort)){

					heaps.add(str);



				}
				else if(s.equals(locsetSort)){
					locsets.add(str);

				}
				else if(s.equals(fieldSort)){
					fields.add(str);

				}



			}
			else{

				for(Term sub : t.subs()){
					countConstants(sub);
				}


			}



		}

		/**
		 * @return the locsets
		 */
		public Set<String> getLocsets() {
			return locsets;
		}

		/**
		 * @return the heaps
		 */
		public Set<String> getHeaps() {
			return heaps;
		}

		/**
		 * @return the fields
		 */
		public Set<String> getFields() {
			return fields;
		}








	}







}
