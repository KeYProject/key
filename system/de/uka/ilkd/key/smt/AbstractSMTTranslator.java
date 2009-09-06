//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.util.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


/**
 * This abstract class provides a stubb for translation of KeY-Formulas to other standards.
 * Formulas are  translated in a correct, but not always complete representation
 * of the target standard.
 * Non-first-order elements in a formula are translated as uninterpreted predicates.
 * 
 * The translation for standards supporting multiple sorts is oriented on the paper 
 * "The Boogie 2 Type System: Design and Verification Condition Generation" 
 * by Leino and Ruemmer.
 * 
 * @author Simon Greiner
 *
 */
public abstract class AbstractSMTTranslator implements SMTTranslator {
    static Logger logger = Logger.getLogger(AbstractSMTTranslator.class
	    .getName());

    private Sort jbyteSort;

    private Sort jshortSort;

    private Sort jintSort;

    private Sort jlongSort;

    private Sort jcharSort;

    private Sort integerSort;
    
    /** The string used as standard sort for translations */
    private final StringBuffer standardSort = new StringBuffer("u");

    // private static long counter = 0;   
    protected static final int YESNOT = 2;

    /** The translation result is stored in this variable. */
    protected String text;

    /** StringBuffer contains all declared predicate symbols. */
    protected final StringBuffer predicate = new StringBuffer();

    /** StringBuffer to store text which could be usefull for the user */
    protected final StringBuffer notes = new StringBuffer();

    /** remember all printed predicates */
    protected final Set<Operator> predicateSet = new HashSet<Operator>();

    /** remember all printed functions */
    protected final Set<Operator> functionSet = new HashSet<Operator>();

    protected final Set<Sort> sortSet = new HashSet<Sort>();

    /** remember all function declarations */

    protected final HashSet usedGlobalMv = new HashSet();

    protected final HashSet usedLocalMv = new HashSet();

    private HashMap<Operator, ArrayList<Sort>> functionDecls = new HashMap<Operator, ArrayList<Sort>>();

    private HashSet<Function> specialFunctions = new HashSet<Function>();
    
    private HashMap<Operator, ArrayList<Sort>> predicateDecls = new HashMap<Operator, ArrayList<Sort>>();

    private HashMap<Operator, StringBuffer> usedVariableNames = new HashMap<Operator, StringBuffer>();

    private HashMap<Operator, StringBuffer> usedFunctionNames = new HashMap<Operator, StringBuffer>();

    private HashMap<Operator, StringBuffer> usedPredicateNames = new HashMap<Operator, StringBuffer>();

    private HashMap<Sort, StringBuffer> usedDisplaySort = new HashMap<Sort, StringBuffer>();

    private HashMap<Sort, StringBuffer> usedRealSort = new HashMap<Sort, StringBuffer>();

    private HashMap<Sort, StringBuffer> typePredicates = new HashMap<Sort, StringBuffer>();

    // used type predicates for constant values, e.g. 1, 2, ...
    private HashMap<Term, StringBuffer> constantTypePreds = new HashMap<Term, StringBuffer>();


    /** map used for storing predicates representing modalities or updates */
    private HashMap<Term, StringBuffer> modalityPredicates = new HashMap<Term, StringBuffer>();
    
    private StringBuffer nullString = new StringBuffer();

    private boolean nullUsed = false;

    //assumptions. they have to be added to the formula!
    private ArrayList<StringBuffer> assumptions = new ArrayList<StringBuffer>();
    
    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with
     * 
     * @param sequent
     *                The sequent which shall be translated.
     * @param services
     * 		      The services object belonging to sequent.
     */
    public AbstractSMTTranslator(Sequent sequent, Services services) {
	jbyteSort = services.getTypeConverter().getByteLDT().targetSort();
	jshortSort = services.getTypeConverter().getShortLDT().targetSort();
	jintSort = services.getTypeConverter().getIntLDT().targetSort();
	jlongSort = services.getTypeConverter().getLongLDT().targetSort();
	jcharSort = services.getTypeConverter().getCharLDT().targetSort();
	integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
    }


    /**
     * For translating only terms and not complete sequents.
     * 		     The service object to be used.
     * @param s
     *  		 
     */
    public AbstractSMTTranslator(Services s) {
	this(null, s);
    }

    /**
     * Translate a sequent into a given syntax.
     * @param sequent the sequent to translate.
     * @param services wrapper object for service attributes.
     * @return A StringBuffer representing the sequent in the given syntax.
     * @throws IllegalFormulaException if the sequent could not be translated.
     */
    public final StringBuffer translate(Sequent sequent, Services services)
	    throws IllegalFormulaException {

	// translate
	StringBuffer hb = new StringBuffer();
	StringBuffer ante;
	ante = translate(sequent.antecedent(), SMTTranslator.TERMPOSITION.ANTECEDENT, services);
	StringBuffer succ;
	succ = translate(sequent.succedent(), SMTTranslator.TERMPOSITION.SUCCEDENT, services);

	//add one variable for each sort
	for (Sort s : this.usedRealSort.keySet()) {
	    LogicVariable l = new LogicVariable(new Name("dummy_" + s.name().toString()), s);
	    this.addFunction(l, new ArrayList<Sort>(), s);
	    this.translateFunc(l, new ArrayList<StringBuffer>());
	}
	
	//ArrayList<StringBuffer> assumptions = this.getAssumptions(services);
	
	hb = this.translateLogicalImply(ante, succ);

	StringBuffer s = buildComplText(services, hb);
	/*StringBuffer s = buildCompleteText(hb, assumptions, this.buildTranslatedFuncDecls(), this
		.buildTranslatedPredDecls(), this.buildTranslatedSorts(), this.buildSortHierarchy());*/
	
	return s;

    }


    
    
    
    /**
     * get the assumptions made by the logic.
     * @param services the services object to be used.
     * @param assumptionTypes  
     * @return ArrayList of Formulas, that are assumed to be true.
     */
    private ArrayList<StringBuffer> getAssumptions(Services services, ArrayList<ContextualBlock> assumptionTypes) throws IllegalFormulaException {
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
	     
	// add the type definitions
	//this means all predicates that are needed for functions to define
	//their result type, all predicates for constants (like number symbols)

	int start = toReturn.size();
	toReturn.addAll(this.getTypeDefinitions());
	assumptionTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION));
	    
	// add the type hierarchy
	//this means, add the typepredicates, that are needed to define
	//for every type, what type they are (direct) subtype of
	start = toReturn.size();
	toReturn.addAll(this.getSortHierarchyPredicates());
	assumptionTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.ASSUMPTION_TYPE_HIERARCHY));
	//add the formulas, that make sure, type correctness is kept, also
	//for interpreted functions
	//leave this away. This is not needed, if interpreted int functions are typed by the second type u
	if (!this.isMultiSorted()) {
	    start = toReturn.size();
	    toReturn.addAll(this.getSpecialSortPredicates(services));
	}
	assumptionTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.ASSUMPTION_SORT_PREDICATES));
	    
	//add the assumptions created during translation
	//for example while translating term if then else
	start = toReturn.size();
	toReturn.addAll(this.assumptions);
	assumptionTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION));
	
	return toReturn;
    }
    
    /**
     * build the formulas, that make sure, special functions keep
     * typing
     * @return ArrayList of formulas, assuring the assumption.
     */
    private ArrayList<StringBuffer> getSpecialSortPredicates(Services services) throws IllegalFormulaException{
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
	
	for (Function o : this.specialFunctions) {
	    
	    ArrayList<StringBuffer> varList = new ArrayList<StringBuffer>();
	    ArrayList<StringBuffer> predList = new ArrayList<StringBuffer>();
	    //build the variables and typepredicates for quantification
	    for (int i = 0; i < o.arity(); i++) {
		StringBuffer var = this.translateLogicalVar(new StringBuffer("tvar" + i));
		varList.add(var);
		ArrayList<StringBuffer> templist = new ArrayList<StringBuffer>();
		templist.add(var);
		StringBuffer temppred = this.typePredicates.get(o.argSort(i));
		predList.add(this.translatePredicate(temppred, templist));
	    }
	    
	    //build the left side of the implication
	    StringBuffer leftForm = predList.get(0);
	    for (int i = 1; i < predList.size(); i++) {
		leftForm = this.translateLogicalAnd(leftForm, predList.get(i));
	    }
	    
	    //build the right side of the implication
	    StringBuffer rightForm = new StringBuffer();
	    
	    //use the interpreted function here!!
	    if (o == services.getTypeConverter().getIntegerLDT().getAdd()) {
		rightForm = this.translateIntegerPlus(varList.get(0), varList.get(1));
	    } else if (o == services.getTypeConverter().getIntegerLDT().getSub()) {
		rightForm = this.translateIntegerMinus(varList.get(0), varList.get(1));
	    } else if (o == services.getTypeConverter().getIntegerLDT().getMul()) {
		rightForm = this.translateIntegerMult(varList.get(0), varList.get(1));
	    } else if (o == services.getTypeConverter().getIntegerLDT().getDiv()) {
		rightForm = this.translateIntegerDiv(varList.get(0), varList.get(1));
	    }
	    
	    StringBuffer rightPred = this.typePredicates.get(o.sort());
	    ArrayList<StringBuffer> tempList = new ArrayList<StringBuffer>();
	    tempList.add(rightForm);
	    rightForm = this.translatePredicate(rightPred, tempList);
	    
	    StringBuffer form = this.translateLogicalImply(leftForm, rightForm);
	    
	    for (int i = 0; i < varList.size(); i++) {
		form = this.translateLogicalAll(varList.get(i), this.getIntegerSort(), form);
	    }
	    
	    toReturn.add(form);
	}
	
	return toReturn;
    }
    
    /**
     * Translate a term into the given syntax.
     * @param t The term to translate.
     * @param services a service wrapper object.
     * @return A StringBuffer, representing the term in the given syntax.
     * @throws IllegalArgumentException if the term is not of type FORMULA or could not be translated.
     */
    public final StringBuffer translate(Term t, Services services) 
    		throws IllegalArgumentException {
	//check, if the term is of type formula. Otherwise a translation does not make sense
	if (t.sort() != Sort.FORMULA) {
	    throw new IllegalArgumentException("The given Term is not Type of Formula");
	}
	 //translate
	try {
	    StringBuffer form;
	    form = translateTerm(t, new Vector<QuantifiableVariable>(), services);
	    return buildComplText(services, form);
	} catch (IllegalFormulaException e) {
	    throw new IllegalArgumentException("Illegal formula. Can not be translated");
	}
    }
    
    private StringBuffer buildComplText(Services serv, StringBuffer formula) throws IllegalFormulaException {
	ArrayList<ContextualBlock> assumptionTypes = new ArrayList<ContextualBlock>();
	ArrayList<ContextualBlock> predicateTypes = new ArrayList<ContextualBlock>();
	return buildCompleteText(formula, this.getAssumptions(serv, assumptionTypes),assumptionTypes, this.buildTranslatedFuncDecls(), this
		    .buildTranslatedPredDecls(predicateTypes),predicateTypes, this.buildTranslatedSorts(), this
		    .buildSortHierarchy());
    }
    
    /**
     * Build the sorthierarchy for the sorts
     * If null was used, add typepredicates for all types.
     * 
     * @return a sort hierarchy for the sorts
     */
    private SortHierarchy buildSortHierarchy() {
	return new SortHierarchy(this.usedDisplaySort, this.typePredicates);
    }

    /**
     * Get the expression for that defines the typepredicates for sort hierarchy.
     * Also the null type is added to the formula if used before.
     * @return The well defined formula.
     */
    private ArrayList<StringBuffer> getSortHierarchyPredicates() {
	SortHierarchy sh = this.buildSortHierarchy();
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
	
	// add the typepredicates for functions.
	HashMap<StringBuffer, ArrayList<StringBuffer>> predMap = sh
		.getDirectSuperSortPredicate();
	for (StringBuffer leftPred : predMap.keySet()) {
	    StringBuffer form = new StringBuffer();
	    for (StringBuffer rightPred : predMap.get(leftPred)) {
		StringBuffer var = this.translateLogicalVar(new StringBuffer(
			"tvar"));
		ArrayList<StringBuffer> varlist = new ArrayList<StringBuffer>();
		varlist.add(var);
		StringBuffer leftForm = this.translatePredicate(leftPred,
			varlist);

		StringBuffer rightForm = this.translatePredicate(rightPred,
			varlist);

		form = this.translateLogicalImply(leftForm, rightForm);
		if (this.isMultiSorted()) {
		    form = this.translateLogicalAll(var, this.standardSort,
			form);
		} else {
		    form = this.translateLogicalAll(var, this.getIntegerSort(),
				form);
		}
	    }
	    if (form.length() > 0) {
		toReturn.add(form);
	    }
	}

	// add the typepredicates for null
	if (this.nullUsed) {
	    for (StringBuffer s : this.typePredicates.values()) {
		ArrayList<StringBuffer> argList = new ArrayList<StringBuffer>();
		argList.add(this.nullString);
		StringBuffer toAdd = this.translatePredicate(s, argList);
		toReturn.add(toAdd);
	    }
	}

	return toReturn;
    }

    /**
     * Returns a set of formula s, that defines the resulttypes of functions,
     * all constants and other elements (i.e. constant number symbols).
     * @return see above
     */
    private ArrayList<StringBuffer> getTypeDefinitions() {
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();

	// add the type definitions for functions
	for (Operator op : functionDecls.keySet()) {
	    StringBuffer currentForm = this.getSingleFunctionDef(
		    this.usedFunctionNames.get(op), functionDecls.get(op));
	    if (currentForm.length() > 0) {
		//Do not add it, if an empty result was returned.
		//might lead to confusions.
		toReturn.add(currentForm);
	    }
	}

	//add the type predicates for constant values like number symbols
	if (!this.isMultiSorted()) {
	    for (StringBuffer s : this.constantTypePreds.values()) {
		toReturn.add(s);
	    }
	}
	
	return toReturn;
    }

    /**
     * Get the type predicate definition for a given function.
     * If the result type is of some int type, empty StringBuffer is returned.
     * 
     * @param funName the name of the function.
     * @param sorts the sorts, the function is defined for. 
     * 		Last element is the return type.
     * @return well formed expression that defines the type of the function.
     */
    private StringBuffer getSingleFunctionDef(StringBuffer funName,
	    ArrayList<Sort> sorts) {
	StringBuffer toReturn = new StringBuffer();

	/*
	 * given: the name of a function and its sorts.
	 * 
	 * in case of MultiSort-mode:
	 * if the functions result is of some non-integer type
	 * returned: for all tvar1:displaysort1,...,tvarn:displaysortn : 
	 * 	[type_of_sort1(tvar1) AND ... type_of_sortn(tvarn)] implies
	 * 	type_of_n+1(funcName(tvar1, ..., tvarn))
	 * 
	 * if one of the arguments are of sort int, skip their type atrribute.
	 * if all of them are, skip lefthandside of the implication
	 * 
	 */
	int firstIndex = -1;
	if (!this.isMultiSorted() || !isSomeIntegerSort(sorts.get(sorts.size()-1))) {
	    // collect the quantify vars
	    ArrayList<StringBuffer> qVar = new ArrayList<StringBuffer>();
	    for (int i = 0; i < sorts.size() - 1; i++) {
		qVar.add(this.translateLogicalVar(new StringBuffer("tvar")));
	    }

	    // left hand side of the type implication
	    if (!this.isMultiSorted()) {
		if (qVar.size() > 0) {
		     toReturn = this.getTypePredicate(sorts.get(0), qVar.get(0));
		}
		for (int i = 1; i < qVar.size(); i++) {
		     StringBuffer temp = getTypePredicate(sorts.get(i), qVar.get(i));
		     toReturn = this.translateLogicalAnd(toReturn, temp);
		}
	    } else {
		//find the first non-int sort
		
		for (int i = 0; i < qVar.size() && firstIndex == -1 ; i++) {
		    if (!isSomeIntegerSort(sorts.get(i))) {
			firstIndex = i;
			toReturn = this.getTypePredicate(sorts.get(i), qVar.get(i));
		    }
		}
	    
		for (int i = firstIndex+1; i < qVar.size() && firstIndex > -1; i++) {
		    if (isSomeIntegerSort(sorts.get(i))){
			StringBuffer temp = getTypePredicate(sorts.get(i), qVar.get(i));
			toReturn = this.translateLogicalAnd(toReturn, temp);
		    }
		}
	    }
	    // build the right side
	    StringBuffer rightSide;
	    rightSide = this.translateFunction(funName, qVar);
	    rightSide = getTypePredicate(sorts.get(sorts.size() - 1), rightSide);

	    if (!this.isMultiSorted()) {
		if (qVar.size() > 0) {
		    toReturn = this.translateLogicalImply(toReturn, rightSide);
		} else {
		    toReturn = rightSide;
		}
	    } else {
		if (firstIndex > -1) {
		    toReturn = this.translateLogicalImply(toReturn, rightSide);
		} else {
		    toReturn = rightSide;
		}
	    }

	    // built the forall around it
	    for (int i = qVar.size() - 1; i >= 0; i--) {
		toReturn = this.translateLogicalAll(qVar.get(i),
			this.usedDisplaySort.get(sorts.get(i)), toReturn);
	    }

	    return toReturn;
	} else {
	    /*
	     * the function is of some int type. Welldefinedness is not needed to be axiomated.
	     * The returntype is defined via the int type, the welldefinedness of the arguments 
	     * is defined by construction (also used above).
	     */
	    return toReturn;
	}
	
    }

    /**
     * Build the translated function declarations. Each element in the
     * ArrayList represents (functionname | argType1 | ... | argTypen|
     * resultType)
     * 
     * @return structured List of declaration.
     */
    private ArrayList<ArrayList<StringBuffer>> buildTranslatedFuncDecls() {
	ArrayList<ArrayList<StringBuffer>> toReturn = new ArrayList<ArrayList<StringBuffer>>();
	//add the function declarations for each used function
	for (Operator op : this.functionDecls.keySet()) {
	    ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
	    element.add(usedFunctionNames.get(op));
	    for (Sort s : functionDecls.get(op)) {
		element.add(usedDisplaySort.get(s));
	    }
	    toReturn.add(element);
	}

	if (this.nullUsed) {
	    //add the null constant to the declarations
	    ArrayList<StringBuffer> a = new ArrayList<StringBuffer>();
	    a.add(this.nullString);
	    if (this.isMultiSorted()) {
		a.add(this.standardSort);
	    } else {
		a.add(this.getIntegerSort());
	    }
	    toReturn.add(a);
	}

	//add the definition of the cast function
	if (this.isMultiSorted() && this.castPredicate != null) {
	    //it was used at least once
	    ArrayList<StringBuffer> temp = new ArrayList<StringBuffer>();
	    temp.add(this.castPredicate);
	    temp.add(this.getIntegerSort());
	    temp.add(this.standardSort);
	    toReturn.add(temp);
	}
	
	
	return toReturn;
    }
    
    /**
     * Build the translated predicate declarations. Each element in the
     * ArrayList represents (predicatename | argType1 | ... | argTypen)
     * 
     * @return structured List of declaration.
     */
    private ArrayList<ArrayList<StringBuffer>> buildTranslatedPredDecls(ArrayList<ContextualBlock> predicateTypes) {
	ArrayList<ArrayList<StringBuffer>> toReturn = new ArrayList<ArrayList<StringBuffer>>();
	
	int start = toReturn.size();
	// add the predicates
	
	for (Operator op : this.predicateDecls.keySet()) {
	    ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
	    element.add(usedPredicateNames.get(op));
	    for (Sort s : predicateDecls.get(op)) {
		element.add(usedDisplaySort.get(s));
	    }
	    toReturn.add(element);
	}
	
        predicateTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.PREDICATE_FORMULA));
	
	// add the typePredicates
        
        start = toReturn.size();
	    
        for (Sort s : this.typePredicates.keySet()) {
            ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
            element.add(typePredicates.get(s));
            if (!this.isMultiSorted()) {
        	element.add(this.usedDisplaySort.get(s));
            } else {
        	//type predicates can only be used for standardSort, never for integer sorts.
        	//always tape cast needed for this.
        	element.add(this.standardSort);
            }
            toReturn.add(element);
	}

        predicateTypes.add(new ContextualBlock(start,toReturn.size()-1,ContextualBlock.PREDICATE_TYPE));	
	return toReturn;
    }

    /**
     * ArrayList of all sorts, that were used as sorts. Including the
     * integer sort.
     * 
     * @return ArrayList of the names of sorts.
     */
    private ArrayList<StringBuffer> buildTranslatedSorts() {
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
	
	if (!this.isMultiSorted()) {
	    for (Sort s : this.usedDisplaySort.keySet()) {
		StringBuffer newSort = this.usedDisplaySort.get(s);
		// make sure, no sort is added twice!!
		boolean alreadyIn = false;
		for (int i = 0; !alreadyIn && i < toReturn.size(); i++) {
		    if (toReturn.get(i).equals(newSort)) {
			alreadyIn = true;
		    }
		}
		if (!alreadyIn) {
		    toReturn.add(newSort);
		}
	    }
	} else {
	    //add the two sorts needed as maximum
	    toReturn.add(this.standardSort);
	    toReturn.add(this.getIntegerSort());
	}
	return toReturn;
    }

    /**
     * Build the text, that can be read by the final decider.
     * If the assumptions should be added to the formula, add them like
     * assumtions impliy formula.
     * 
     * @param formula
     *                The formula, that was built out of the internal
     *                representation. It is built by ante implies succ.
     * @param assumptions
     * 		      Assumptions made in this logic. Set of formulas, that
     * 		      are assumed to be true.      
     * @param assumptionBlocks
     * 		      List of ContextualBlocks, which refer to the position of different
     * 		      types of assumptions in the container <code>assumptions</code>.
     *                Use these objects to make detailed 
     * 		      comments in the translations. For more information see the class <code>ContextualBlock</code>.  
     * @param functions
     *                List of functions. Each Listelement is built up like
     *                (name | sort1 | ... | sortn | resultsort)
     * @param predicates
     *                List of predicates. Each Listelement is built up like
     *                (name | sort1 | ... | sortn)
     * @param predicateBlocks
     * 		      List of ContextualBlocks, which refer to the position of different
     * 		      types of predicate in the container <code>predicates</code>.
     *                Use these objects to make detailed 
     * 		      comments in the translations. For more information see the class <code>ContextualBlock</code>.  
     * @param types
     *                List of the used types.
     * @return The Stringbuffer that can be read by the decider
     */
    protected abstract StringBuffer buildCompleteText(StringBuffer formula,
	    ArrayList<StringBuffer> assumptions,
	    ArrayList<ContextualBlock> assumptionBlocks,
	    ArrayList<ArrayList<StringBuffer>> functions,
	    ArrayList<ArrayList<StringBuffer>> predicates,
	    ArrayList<ContextualBlock> predicateBlocks,
	    ArrayList<StringBuffer> types, SortHierarchy sortHierarchy);

    /**
     * Translates the given Semisequent into "Simplify" input syntax and
     * adds the resulting string to the StringBuffer sb.
     * 
     * @param semi
     *                the SemiSequent which should be written in Simplify
     *                syntax
     */
    private final StringBuffer translate(Semisequent semi, SMTTranslator.TERMPOSITION skolemization, Services services)
	    throws IllegalFormulaException {
	StringBuffer hb = new StringBuffer();

	// if the sequent is empty, return true/false as formula
	if (semi.size() == 0) {
	    if (skolemization == SMTTranslator.TERMPOSITION.ANTECEDENT) {
		hb.append(translateLogicalTrue());
	    } else {
		hb.append(translateLogicalFalse());
	    }
	    return hb;
	}

	// translate the first semisequence
	hb = translate(semi.get(0), services);

	// translate the other semisequences, juncted with AND or OR
	for (int i = 1; i < semi.size(); ++i) {
	    if (skolemization == SMTTranslator.TERMPOSITION.ANTECEDENT) {
		hb = translateLogicalAnd(hb, translate(semi.get(i), services));
	    } else {
		hb = translateLogicalOr(hb, translate(semi.get(i), services));
	    }
	}

	return hb;
    }
    
    /**
     * Translates the given ConstrainedFormula into "Simplify" input syntax
     * and adds the resulting string to the StringBuffer sb.
     * 
     * @param cf
     *                the ConstrainedFormula which should be written in
     *                given syntax
     */
    private final StringBuffer translate(ConstrainedFormula cf, Services services)
	    throws IllegalFormulaException {
	StringBuffer hb = new StringBuffer();
	Term t;
	t = cf.formula();
	Operator op = t.op();
	hb.append(translateTerm(t, new Vector<QuantifiableVariable>(), services));
	return hb;
    }
    
    /**
     * Returns, whether the Structure, this translator creates should be a
     * Structure, that is multi sorted. If false, a single sorted structure 
     * is created. Then all sorts are translated as integers.
     * 
     * @return true, if multi sorted logic is supported.
     */
    protected abstract boolean isMultiSorted();

    /**
     * The String used for integer values. This sort is also used in single
     * sorted logics.
     * 
     * @return The String used for integers.
     */
    protected abstract StringBuffer getIntegerSort();

    /**
     * Build the Stringbuffer for a logical NOT.
     * 
     * @param arg
     *                The Formula to be negated.
     * @return The StringBuffer representing the resulting Formular
     */
    protected abstract StringBuffer translateLogicalNot(StringBuffer arg);

    /**
     * Build the logical konjunction.
     * 
     * @param arg1
     *                The first formula.
     * @param arg2
     *                The second formula.
     * @return The StringBuffer representing the resulting formular.
     */
    protected abstract StringBuffer translateLogicalAnd(StringBuffer arg1,
	    StringBuffer arg2);

    /**
     * Build the logical disjunction.
     * 
     * @param arg1
     *                The first formula.
     * @param arg2
     *                The second formula.
     * @return The StringBuffer representing the resulting formular.
     */
    protected abstract StringBuffer translateLogicalOr(StringBuffer arg1,
	    StringBuffer arg2);

    /**
     * Build the logical implication.
     * 
     * @param arg1
     *                The first formula.
     * @param arg2
     *                The second formula.
     * @return The StringBuffer representing the resulting formular
     */
    protected abstract StringBuffer translateLogicalImply(StringBuffer arg1,
	    StringBuffer arg2);

    /**
     * Build the logical equivalence.
     * 
     * @param arg1
     *                The first formula.
     * @param arg2
     *                The second formula.
     * @return The StringBuffer representing the resulting formular
     */
    protected abstract StringBuffer translateLogicalEquivalence(
	    StringBuffer arg1, StringBuffer arg2);

    /**
     * Build the logical forall formula.
     * 
     * @param var
     *                the bounded variable.
     * @param type
     *                the type of the bounded variable.
     * @param form
     *                The formula containing the bounded variable.
     * @return The resulting formula.
     */
    protected abstract StringBuffer translateLogicalAll(StringBuffer var,
	    StringBuffer type, StringBuffer form);

    /**
     * Build the logical exists formula.
     * 
     * @param var
     *                the bounded variable.
     * @param type
     *                the type of the bounded variable.
     * @param form
     *                The formula containing the bounded variable.
     * @return The resulting formula.
     */
    protected abstract StringBuffer translateLogicalExist(StringBuffer var,
	    StringBuffer type, StringBuffer form);

    /**
     * Translate the logical true.
     * 
     * @return The StringBuffer the logical true value.
     */
    protected abstract StringBuffer translateLogicalTrue();

    /**
     * Translate the logical false.
     * 
     * @return The StringBuffer the logical false value.
     */
    protected abstract StringBuffer translateLogicalFalse();

    /**
     * Build the Stringbuffer for an object equivalence.
     * 
     * @param arg1
     *                The first formula of the equivalence.
     * @param arg2
     *                The second formula of the equivalence.
     * @return The StringBuffer representing teh resulting Formular
     */
    protected abstract StringBuffer translateObjectEqual(StringBuffer arg1,
	    StringBuffer arg2);

    /**
     * Build the Stringbuffer for an variable.
     * 
     * @return The StringBuffer representing the resulting Formular
     */
    protected abstract StringBuffer translateLogicalVar(StringBuffer name);

    /**
     * Build the Stringbuffer for an constant.
     * 
     * @return The StringBuffer representing the resulting Formular
     */
    protected abstract StringBuffer translateLogicalConstant(StringBuffer name);

    /**
     * Translate a predicate.
     * 
     * @param name
     *                The Symbol of the predicate.
     * @param args
     *                The arguments of the predicate.
     * @return the formula representing the predicate.
     */
    protected abstract StringBuffer translatePredicate(StringBuffer name,
	    ArrayList<StringBuffer> args);

    /**
     * Get the name for a predicate symbol.
     * 
     * @param name
     *                The name that can be used to create the symbol.
     * @return The unique predicate symbol.
     */
    protected abstract StringBuffer translatePredicateName(StringBuffer name);

    /**
     * Translate a function.
     * 
     * @param name
     *                The Symbol of the function.
     * @param args
     *                The arguments of the function.
     * @return the formula representing the function.
     */
    protected abstract StringBuffer translateFunction(StringBuffer name,
	    ArrayList<StringBuffer> args);

    /**
     * Get the name for a function symbol.
     * 
     * @param name
     *                The name that can be used to create the symbol.
     * @return The unique function symbol.
     */
    protected abstract StringBuffer translateFunctionName(StringBuffer name);

    /**
     * Translate the integer plus.
     * 
     * @param arg1
     *                first val of the sum.
     * @param arg2
     *                second val of the sum.
     * @return The formula representing the integer plus.
     */
    protected StringBuffer translateIntegerPlus(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer addition is not supported by this translator.");

    }

    /**
     * Translate the integer minus.
     * 
     * @param arg1
     *                The first val of the substraction.
     * @param arg2
     *                second val of the substraction.
     * @return The formula representing the integer substraction.
     */
    protected StringBuffer translateIntegerMinus(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {
	
	throw new IllegalFormulaException("Integer subtraction is not supported by this translator.");

    }

    /**
     * Translate a unary minus.
     * 
     * @param arg
     *                the argument of the unary minus.
     * @return the formula representing tha unary minus function.
     */
    protected StringBuffer translateIntegerUnaryMinus(StringBuffer arg) 
    	throws IllegalFormulaException {
	
	throw new IllegalFormulaException("negative numbers are not supported by this translator.");

    }

    /**
     * Translate the integer multiplication.
     * 
     * @param arg1
     *                The first val of the multiplication.
     * @param arg2
     *                second val of the multiplication.
     * @return The formula representing the integer multiplication.
     */
    protected StringBuffer translateIntegerMult(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer multiplication is not supported by this translator.");

    }

    /**
     * Translate the integer division.
     * Override this, if integer division is supported.
     * 
     * @param arg1
     *                The first val of the division.
     * @param arg2
     *                second val of the division.
     * @return The formula representing the integer division.
     */
    protected StringBuffer translateIntegerDiv(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer division is not supported by this translator.");

    }

    /**
     * Translate the integer modulo.
     * Override this, if integer modulo is supported.
     * 
     * @param arg1
     *                The first val of the modulo.
     * @param arg2
     *                second val of the modulo.
     * @return The formula representing the integer modulo.
     */
    protected StringBuffer translateIntegerMod(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer modulo is not supported by this translator.");

    }

    /**
     * Translate the greater than.
     * Override this, if integer greater is supported.
     * 
     * @param arg1
     *                The first val of the greater than.
     * @param arg2
     *                second val of the greater than.
     * @return The formula representing the greater than.
     */
    protected StringBuffer translateIntegerGt(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {
	    
	throw new IllegalFormulaException("Integer greater is not supported by this translator.");

    }

    /**
     * Translate the less than.
     * Override this, if integer less is supported.
     * 
     * @param arg1
     *                The first val of the less than.
     * @param arg2
     *                second val of the less than.
     * @return The formula representing the less than.
     */
    protected StringBuffer translateIntegerLt(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer less is not supported by this translator.");

    }

    /**
     * Translate the greater or equal.
     * Override this, if integer greater or equal is supported.
     * 
     * @param arg1
     *                The first val of the greater or equal.
     * @param arg2
     *                second val of the greater or equal.
     * @return The formula representing the greater or equal.
     */
    protected StringBuffer translateIntegerGeq(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer greater or equal is not supported by this translator.");

    }

    /**
     * Translate the less or equal.
     * Override this, if integer less or equal is supported.
     * 
     * @param arg1
     *                The first val of the less or equal.
     * @param arg2
     *                second val of the less or equal.
     * @return The formula representing the less or equal.
     */
    protected StringBuffer translateIntegerLeq(StringBuffer arg1,
	    StringBuffer arg2) throws IllegalFormulaException {
	    
	throw new IllegalFormulaException("Integer less or equal is not supported by this translator.");

    }

    /**
     * Translate the NULL element
     * 
     * @return the Stringbuffer used for nullelement
     */
    protected abstract StringBuffer translateNull();

    /**
     * Translate the NULL element's Sort.
     * 
     * @return the StringBuffer used for Null.
     */
    protected abstract StringBuffer translateNullSort();

    /**
     * Translate a sort.
     * 
     * @param name
     *                the sorts name
     * @param isIntVal
     *                true, if the sort should represent some kind of
     *                integer
     * 
     * @return The String used for this sort. If Multisorted, used in
     *         declarations, else for the typepredicates.
     */
    protected abstract StringBuffer translateSort(String name, boolean isIntVal);

    /**
     * Translate a sort. Return the StringBuffer, that should be displayed
     * at definitionpart. i.e. the name used for typepredicates an similair.
     * Override this, if integers are supported.
     * 
     * @return the sorts name
     */
    protected StringBuffer translateIntegerValue(long val) throws IllegalFormulaException {

	throw new IllegalFormulaException("Integer numbers are not supported by this translator.");

    }

    /**
     * Translate the logical if_then_else construct. 
     * All attributes are logical formulas.
     * If the underlying language does not support this contruct, it is equivalent with
     * (cond IMPLIES ifterm) AND (NOT(cond) IMPLIES thenterm) and can be reduced to this.
     * @param cond the condition term.
     * @param ifterm the formula used, if cond=true
     * @param elseterm the term used, if cond=false
     * @return ther StringBuffer representing the if then else construct
     */
    protected abstract StringBuffer translateLogicalIfThenElse(StringBuffer cond, StringBuffer ifterm, StringBuffer elseterm);
        
    /**
     * Translate the if_then_else construct for terms (i.e. ifterm and condterm are not of Sort FORMULA)
     * If this method is nor overriden, a default implementation is used. This might me less effective than
     * a language supported translation. So, if allowed by the target language, override this.
     * @param cond the condition formula
     * @param ifterm the term used if cond = true.
     * @param elseterm the term used if cond = false.
     * @return the StringBuffer representing the if then else construct.
     * @throws IllegalFormulaException if this construct is not supported.
     */
    protected StringBuffer translateTermIfThenElse (StringBuffer cond, StringBuffer ifterm, StringBuffer elseterm) 
    	throws IllegalFormulaException {

	throw new IllegalFormulaException("The if then else construct for terms is not supported");

    }
    
    private final StringBuffer translateTermIte (Term iteTerm, Vector<QuantifiableVariable> quantifiedVars,
	    Services services) throws IllegalFormulaException {
	
	//make typecasts, if this is neccesary. Subterms might contain integer values,
	//but object values are needed
	StringBuffer cond = translateTerm(iteTerm.sub(0), quantifiedVars, services);
	StringBuffer ifterm = translateTerm(iteTerm.sub(1), quantifiedVars, services);
	if (this.isMultiSorted()) {
	    ifterm = this.castIfNeccessary(ifterm, iteTerm.sub(1).sort(), iteTerm.sort());
	}
	StringBuffer elseterm = translateTerm(iteTerm.sub(2), quantifiedVars, services);
	if (this.isMultiSorted()) {
	    elseterm = this.castIfNeccessary(elseterm, iteTerm.sub(2).sort(), iteTerm.sort());
	}
	try {
	    return this.translateTermIfThenElse(cond, ifterm, elseterm);
	} catch (IllegalFormulaException e) {
	    //the translation of if then else for terms is not supported, so use default implementation
	    //invent a new constant
	    LogicVariable c = new LogicVariable(new Name("iteConst"), iteTerm.sort());
	    //translate the constant
	    Term t = new TermFactory().createVariableTerm(c);
	    StringBuffer cstr = this.translateTerm(t, quantifiedVars, services);
	    //build an assumption used to specify how c can be used
	    StringBuffer assump = this.translateObjectEqual(cstr, ifterm);
	    assump = this.translateLogicalImply(cond, assump);
	    StringBuffer temp = this.translateObjectEqual(cstr, elseterm);
	    temp = this.translateLogicalImply(
		    this.translateLogicalNot(cond), temp);
	    assump = this.translateLogicalAnd(assump, temp);
	    this.assumptions.add(assump);
	    
	    return cstr;
	}
    }
    
    /**
     * CAUTION: Do not use this method from outside this class!!
     * It is public just for test reasons! It will be private very soon!
     * 
     * Translates the given term into input syntax and adds the resulting
     * string to the StringBuffer sb.
     * 
     * @param term
     *                the Term which should be written in Simplify syntax
     * @param quantifiedVars
     *                a Vector containing all variables that have been bound
     *                in super-terms. It is only used for the translation of
     *                modulo terms, but must be looped through until we get
     *                there.
     */
//  TODO make private again after testing!!
    public final StringBuffer translateTerm (Term term, Vector<QuantifiableVariable> quantifiedVars,
	    Services services) throws IllegalFormulaException {
	
	//added, because meatavariables should not be translated.
	if (term.op() instanceof Metavariable) {
	    throw new IllegalFormulaException("The Formula contains a metavariable:\n" +
	    		term.op().toString() + "\n" +
	    		"Metavariables can not be translated.");
	}
	
	Operator op = term.op();
	if (op == Op.NOT) {
	    StringBuffer arg = translateTerm(term.sub(0), quantifiedVars, services);
	    return this.translateLogicalNot(arg);
	} else if (op == Op.AND) {
	    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars, services);
	    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars, services);
	    return this.translateLogicalAnd(arg1, arg2);
	} else if (op == Op.OR) {
	    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars, services);
	    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars, services);
	    return this.translateLogicalOr(arg1, arg2);
	} else if (op == Op.IMP) {
	    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars, services);
	    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars, services);
	    return this.translateLogicalImply(arg1, arg2);
	} else if (op == Op.EQV) {
	    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars, services);
	    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars, services);
	    return this.translateLogicalEquivalence(arg1, arg2);
	} else if (op == Op.EQUALS) {
	    /*
	     * Make a cast on the subterms, if one is of int type, the other is not
	     */
	    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars, services);
	    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars, services);
	    if (this.isMultiSorted() && isSomeIntegerSort(term.sub(0).sort()) 
		    && !isSomeIntegerSort(term.sub(1).sort())) {
		arg1 = cast(arg1);
	    }
	    if (this.isMultiSorted() && !isSomeIntegerSort(term.sub(0).sort()) 
		    && isSomeIntegerSort(term.sub(1).sort())) {
		arg2 = cast(arg2);
	    }
	    return this.translateObjectEqual(arg1, arg2);
	} else if (op instanceof Modality) {
	    //op is a modality. So translate it as an uninterpreted predicate.
	    //equal modalities are translated with the same predicate
	    return this.getModalityPredicate(term, quantifiedVars, services);
	} else if (op instanceof QuanUpdateOperator) {
	    //op is a update. So translate it as an uninterpreted predicate.
	    //equal updates are translated with the same predicate.
	    return this.getModalityPredicate(term, quantifiedVars, services);
	} else if (op == Op.IF_THEN_ELSE) {
	    if (term.sub(1).sort() == Sort.FORMULA) {
		//a logical if then else was used
		StringBuffer cond = translateTerm(term.sub(0), quantifiedVars, services);
		StringBuffer ifterm = translateTerm(term.sub(1), quantifiedVars, services);
		StringBuffer elseterm = translateTerm(term.sub(2), quantifiedVars, services);
		return translateLogicalIfThenElse(cond, ifterm, elseterm);
	    } else {
		//a term if then else was used
		return this.translateTermIte(term, quantifiedVars, services);
	    }
	} else if (op == Op.ALL) {
	    ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
	    Debug.assertTrue(vars.size() == 1);

	    quantifiedVars.add(vars.get(0));

	    StringBuffer qv = this.translateVariable(vars
		    .get(0));
	    StringBuffer sort = this.translateSort(vars
		    .get(0).sort());
	    StringBuffer form = this.translateTerm(term.sub(0), quantifiedVars,
		    services);

	    if (!this.isMultiSorted() || !isSomeIntegerSort(vars.getQuantifiableVariable(0).sort())) {
		// add the typepredicate
		// this is not needed, if the variable, that is quantified over is of
		// some integer type and in Multisort mode
		form = this.translateLogicalImply(this.getTypePredicate(vars
			.get(0).sort(), qv), form);
	    }

	    quantifiedVars.remove(vars.get(0));

	    return this.translateLogicalAll(qv, sort, form);

	} else if (op == Op.EX) {
	    ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
	    Debug.assertTrue(vars.size() == 1);

	    quantifiedVars.add(vars.get(0));

	    StringBuffer qv = this.translateVariable(vars
		    .get(0));
	    StringBuffer sort = this.translateSort(vars
		    .get(0).sort());
	    StringBuffer form = this.translateTerm(term.sub(0), quantifiedVars,
		    services);

	    if (!this.isMultiSorted() || !isSomeIntegerSort(vars.getQuantifiableVariable(0).sort())) {
		// add the typepredicate
		// a and is needed!!
		//This is not the case, if the variable, that is quantified ofer is of some
		// integer type
		form = this.translateLogicalAnd(this.getTypePredicate(vars
			.get(0).sort(), qv), form);
	    }
	    quantifiedVars.remove(vars.get(0));

	    return this.translateLogicalExist(qv, sort, form);
	} else if (op == Op.TRUE) {
	    return this.translateLogicalTrue();
	} else if (op == Op.FALSE) {
	    return this.translateLogicalFalse();
	} else if (op == Op.NULL) {
	    this.nullString = this.translateNull();
	    this.nullUsed = true;
	    return this.nullString;
	} else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
	    // translate as variable or constant
	    if (quantifiedVars.contains(op)) {
		// This variable is used in the scope of a
		// quantifier
		// so translate it as a variable
		return (translateVariable(op));
	    } else {
		// this Variable is a free Variable.
		// translate it as a constant.
		ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
		for (int i = 0; i < op.arity(); i++) {
		    subterms.add(translateTerm(term.sub(i), quantifiedVars,
			    services));
		}

		addFunction(op, new ArrayList<Sort>(), term.sort());

		return translateFunc(op, subterms);
	    }
	} else if (op instanceof Function) {
	    Function fun = (Function) op;
	    if (fun.sort() == Sort.FORMULA) {
		// This Function is a predicate, so translate it
		// as such
		if (fun == services.getTypeConverter().getIntegerLDT()
			.getLessThan()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    return this.translateIntegerLt(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getGreaterThan()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    return this.translateIntegerGt(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getLessOrEquals()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    return this.translateIntegerLeq(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getGreaterOrEquals()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    return this.translateIntegerGeq(arg1, arg2);
		} else {
		    //op is non rigid, so it can be treated as uniterpreted predicate
		    ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
		    for (int i = 0; i < op.arity(); i++) {
			StringBuffer subterm = translateTerm(term.sub(i), quantifiedVars,
				services);
			//add the typecast, if needed
			if (this.isMultiSorted()) {
			    subterm = this.castIfNeccessary(subterm, term.sub(i).sort(), fun.argSort(i));
			}
			subterms.add(subterm);
		    }
		    ArrayList<Sort> sorts = new ArrayList<Sort>();
		    for (int i = 0; i < fun.arity(); i++) {
			sorts.add(fun.argSort(i));
		    }
		    this.addPredicate(fun, sorts);

		    return translatePred(op, subterms);
		}
	    } else {
		// this Function is a function, so translate it
		// as such
		if (fun == services.getTypeConverter().getIntegerLDT().getAdd()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    //add the function to the used ones
		    this.addSpecialFunction(fun);
		    //return the final translation
		    return this.translateIntegerPlus(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getSub()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		    //add the function to the used ones
		    this.addSpecialFunction(fun);
		    //return the final translation
		    return this.translateIntegerMinus(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getNeg()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    return this.translateIntegerUnaryMinus(arg1);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getMul()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		  //add the function to the used ones
		    this.addSpecialFunction(fun);
		    //return the final translation
		    return this.translateIntegerMult(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getDiv()) {
		    StringBuffer arg1 = translateTerm(term.sub(0), quantifiedVars,
			    services);
		    StringBuffer arg2 = translateTerm(term.sub(1), quantifiedVars,
			    services);
		  //add the function to the used ones
		    this.addSpecialFunction(fun);
		    //return the final translation
		    return this.translateIntegerDiv(arg1, arg2);
		} else if (fun == services.getTypeConverter().getIntegerLDT()
			.getNumberSymbol()) {
		    Debug.assertTrue(term.arity() == 1);
		    long num = NumberTranslation.translate(term.sub(0))
			    .longValue();
		    StringBuffer numVal = translateIntegerValue(num);
		    
		    // add the type predicate for this
		    // constant
		    if (!this.constantTypePreds.containsKey(term)) {
			this.translateSort(term.sort());
			StringBuffer typePred = this.getTypePredicate(term
				.sort(), numVal);
			this.constantTypePreds.put(term, typePred);
		    }

		    return numVal;
		} else {
		    // an uninterpreted function. just
		    // translate it as such
		    ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
		    for (int i = 0; i < fun.arity(); i++) {
			//make type casts, if neccessary
			StringBuffer subterm = translateTerm(term.sub(i), quantifiedVars,
				services);
			if (this.isMultiSorted()) {
			    subterm = this.castIfNeccessary(subterm, term.sub(i).sort(), fun.argSort(i));
			}
			subterms.add(subterm);
		    }
		    ArrayList<Sort> sorts = new ArrayList<Sort>();
		    for (int i = 0; i < fun.arity(); i++) {
			sorts.add(fun.argSort(i));
		    }
		    this.addFunction(fun, sorts, fun.sort());

		    return translateFunc(fun, subterms);
		}
	    }

	} else if (op instanceof ArrayOp) {
	    ArrayOp operation = (ArrayOp) op;
	    StringBuffer refPrefix = this.translateTerm(operation
		    .referencePrefix(term), quantifiedVars, services);
	    StringBuffer loc = this.translateTerm(operation.index(term),
		    quantifiedVars, services);
	    ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
	    subterms.add(refPrefix);
	    subterms.add(loc);

	    //no typecast is needed, as the functions sorts are defined
	    //over its arguments sorts.
	    ArrayList<Sort> sorts = new ArrayList<Sort>();
	    sorts.add(operation.referencePrefix(term).sort());
	    sorts.add(operation.index(term).sort());

	    this.addFunction(operation, sorts, operation.sort());

	    return translateFunc(operation, subterms);
	} else if (op instanceof AttributeOp) {
	    AttributeOp atop = (AttributeOp) op;
	    ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
	    for (int i = 0; i < atop.arity(); i++) {
		//a type cast here is never needed, as the function's sorts 
		//are defined over its arguments sorts.
		StringBuffer subTerm = translateTerm(term.sub(i), quantifiedVars, services);
		subterms.add(subTerm);
	    }
	    ArrayList<Sort> sorts = new ArrayList<Sort>();
	    for (int i = 0; i < op.arity(); i++) {
		sorts.add(term.sub(i).sort());
	    }
	    this.addFunction(atop, sorts, atop.sort());

	    return translateFunc(atop, subterms);
	} else {
	    //if none of the above works, the symbol can be translated as uninterpreted function
	    //or predicate. The idea is, tht if a formula is valid with a interpreted function,
	    //it has to be valid with an uninterpreted.
	    //Caution: Counterexamples might be affected by this.
	    return translateUnknown(term, quantifiedVars, services);
	}
    }
    
    /** This stringbuffer is used as predicate name for casts from int-valued to u-valued obects */
    private StringBuffer castPredicate;
    
    /**
     * This method adds a type cast to a translated formula, if neccessary.
     * It is neccesary, if the formula is of some int sort, but some not-int sort
     * is expected. In this case add the type cast.
     * 
     * In general, it is also neccesary to add a type cast, if the formula has some 
     * non-int sort and some int sort is expected. But this should never happen, as
     * ever possible translation is made with int-sort.
     * 
     * A type-cast is never neccessary, if the translation can make use of multisort.
     * 
     * @param formula The formula, that was translated.
     * @param formulaSort The sort, the translatet formula has.
     * @param targetSort The sort, the translated formula is expected to have.
     * @return A stringBuffer containing a type cast, if neccessary.
     */
    private StringBuffer castIfNeccessary(StringBuffer formula, Sort formulaSort, Sort targetSort) {
	if (!this.isMultiSorted()) {
	    return formula;
	}
	if (isSomeIntegerSort(formulaSort) && !isSomeIntegerSort(targetSort)) {
	    return this.cast(formula);
	} else if (!isSomeIntegerSort(formulaSort) && isSomeIntegerSort(targetSort)) {
	    throw new RuntimeException("Error while translation.\n" +
				"Not possible to perform a typecast\n" +
				"for the formula " + formula + "\n" +
				"from type " + formulaSort.toString() + "\n" +
				"to type " + targetSort.toString() + "\n" +
				"Heavy internal error. Notify the administrator of the KeY tool.");
	} else {
	    return formula;
	}
    }
    
    /**
     * Cast a formula of type int to type u.
     * This cast is only performed, if multisort is not suppoerted
     * @param formula the formula to cast.
     * @return the casted formula.
     */
    private StringBuffer cast(StringBuffer formula) {
	if (this.castPredicate == null) {
	    this.castPredicate = this.translateFunctionName(
		    new StringBuffer("castInt2U"));
	}
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(formula);
	return this.translatePredicate(this.castPredicate, args);
    }
    
    /**
     * Get a predicate representing a modality. Make sure that equal modalities 
     * return the same predicate.
     * @param t The term representing the modality.
     * @param quantifiedVars quantified variables.
     * @param services the services object to use.
     * @return a unique predicate representing a modality.
     */
    private StringBuffer getModalityPredicate(Term t, Vector<QuantifiableVariable> quantifiedVars,
	    Services services) throws IllegalFormulaException{
	//check, if the modality was already translated.
	for (Term toMatch : modalityPredicates.keySet()) {
	    if (toMatch.equalsModRenaming(t)) {		
		return modalityPredicates.get(toMatch);
	    }
	}

	//if the program comes here, term has to be translated.
	
	TermFactory tf = new TermFactory();

	//Collect all free Variable in the term
	final ImmutableSet<QuantifiableVariable> freeVars = t.freeVars();
	QuantifiableVariable[] args = freeVars.toArray(new QuantifiableVariable[freeVars.size()]);
	Term[] subs = new Term[args.length];
	Sort[] argsorts = new Sort[args.length];
	for (int i = 0; i < args.length; i++) {
	    QuantifiableVariable qv = args[i];
	    if (qv instanceof LogicVariable) {
		LogicVariable lv = (LogicVariable)qv;
		subs[i] = tf.createVariableTerm(lv);
		argsorts[i] = lv.sort();
	    } else {
		logger.error("Schema variable found in formula.");
	    }
	}
	//invent a new predicate
	Function fun = new NonRigidFunction(new Name("modConst"), t.sort(), argsorts);
	
	//Build the final predicate
	Term temp = tf.createFunctionTerm(fun, subs);
	
	//translate the predicate
	StringBuffer cstr = this.translateTerm(temp, quantifiedVars, services);
	    
	modalityPredicates.put(t, cstr);
	    
	return cstr;
	
    }
    
    /**
     * Add an interpreted function to the set of special functions.
     * Caution: If added here, make sure to handle the function in 
     * getSpecialSortPredicates()
     * @param fun the interpreted function to be added.
     */
    private void addSpecialFunction(Function fun) {
	if (!specialFunctions.contains(fun)) {
		specialFunctions.add(fun);
	    }
    }
    
    /**
     * Get the type predicate for the given sort and the given expression.
     * @param s The sort, the type predicate is wanted for.
     * @param arg The expression, whose type should be defined.
     * @return The well formed type predicate expression.
     */
    private StringBuffer getTypePredicate(Sort s, StringBuffer arg) {
	ArrayList<StringBuffer> arguments = new ArrayList<StringBuffer>();
	arguments.add(arg);
	StringBuffer toReturn = this.translatePredicate(typePredicates.get(s),
		arguments);

	return toReturn;
    }

    /**
     * Takes care of sequent tree parts that were not matched in
     * translate(term, skolemization). In this class it just produces a
     * warning, nothing more. It is provided as a hook for subclasses.
     * 
     * @param term
     *                The Term given to translate
     * @throws IllegalFormulaException
     */
    protected final StringBuffer translateUnknown(Term term, Vector<QuantifiableVariable> quantifiedVars,
	    Services services)
	    throws IllegalFormulaException {
	
	//translate the term as uninterpreted function/predicate
	    Operator op = term.op();
	    if (term.sort() == Sort.FORMULA) {
		//predicate
		logger.debug("Translated as uninterpreted predicate:\n" + term.toString());
		ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
		for (int i = 0; i < op.arity(); i++) {
		    subterms.add(translateTerm(term.sub(i), quantifiedVars,
				services));
		}
		ArrayList<Sort> sorts = new ArrayList<Sort>();
		for (int i = 0; i < op.arity(); i++) {
		    sorts.add(term.sub(i).sort());
		}
		this.addPredicate(op, sorts);

		return translatePred(op, subterms);
	    } else {
		//function
		logger.debug("Translated as uninterpreted function:\n" + term.toString());
		ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
		for (int i = 0; i < op.arity(); i++) {
		    subterms.add(translateTerm(term.sub(i), quantifiedVars,
			services));
		}
		ArrayList<Sort> sorts = new ArrayList<Sort>();
		for (int i = 0; i < op.arity(); i++) {
		    sorts.add(term.sub(i).sort());
		}
		this.addFunction(op, sorts, term.sort());

		return translateFunc(op, subterms);
	    }
    }

    protected final StringBuffer translateVariable(Operator op) {
	if (usedVariableNames.containsKey(op)) {
	    return usedVariableNames.get(op);
	} else {
	    StringBuffer var = this.translateLogicalVar(new StringBuffer(op
		    .name().toString()));
	    usedVariableNames.put(op, var);
	    return var;
	}
    }

    /**
     * translate a function.
     * 
     * @param o
     *                the Operator used for this function.
     * @param sub
     *                The StringBuffers representing the arguments of this
     *                Function.
     * @return a StringBuffer representing the complete Function.
     */
    protected final StringBuffer translateFunc(Operator o,
	    ArrayList<StringBuffer> sub) {
	StringBuffer name;
	if (usedFunctionNames.containsKey(o)) {
	    name = usedFunctionNames.get(o);
	} else {
	    name = translateFunctionName(new StringBuffer(o.name().toString()));
	    usedFunctionNames.put(o, name);
	}
	return translateFunction(name, sub);
    }
    
    /**
     * 
     * @param op the operator used for this function.
     * @param sorts the list of sort parameter of this function
     * @result the function's result sort
     */
    private void addFunction(Operator op, ArrayList<Sort> sorts, Sort result) {
	if (!this.functionDecls.containsKey(op)) {
	    sorts.add(result);
	    this.functionDecls.put(op, sorts);
	    // add all sorts
	    for (Sort s : sorts) {
		this.translateSort(s);
	    }
	}
    }

    private void addPredicate(Operator op, ArrayList<Sort> sorts) {
	if (!this.predicateDecls.containsKey(op)) {
	    this.predicateDecls.put(op, sorts);
	    //add all sorts
	    for (Sort s : sorts) {
		this.translateSort(s);
	    }
	}
    }

    /**
     * Translate a predicate.
     * @param o the operator used for this predicate.
     * @param sub The terms representing the arguments.
     * @return a StringBuffer representing the complete predicate.
     */
    private final StringBuffer translatePred(Operator o,
	    ArrayList<StringBuffer> sub) {
	StringBuffer name;
	if (usedPredicateNames.containsKey(o)) {
	    name = usedPredicateNames.get(o);
	} else {
	    name = translatePredicateName(new StringBuffer(o.name().toString()));
	    usedPredicateNames.put(o, name);
	}
	return translatePredicate(name, sub);
    }

    private final StringBuffer translateSort(Sort s) {
	if (usedDisplaySort.containsKey(s)) {
	    return usedDisplaySort.get(s);
	} else {
	    StringBuffer sortname = this.translateSort(s.name().toString(),
		    isSomeIntegerSort(s));
	    StringBuffer displaysort;

	    if (!this.isMultiSorted()) {
		displaysort = this.getIntegerSort();
	    } else {
		if (isSomeIntegerSort(s)) {
		    displaysort = this.getIntegerSort();
		} else {
		    displaysort = this.standardSort;
		}
	    }
		
	    StringBuffer realsort = sortname;

	    usedDisplaySort.put(s, displaysort);
	    usedRealSort.put(s, realsort);
	    addTypePredicate(realsort, s);

	    return displaysort;
	}
    }

    /**
     * Create a type predicate for a given sort.
     * @param sortname the name, that should be used for the sort.
     * @param s the sort, this predicate belongs to.
     */
    private void addTypePredicate(StringBuffer sortname, Sort s) {
	if (!this.typePredicates.containsKey(s)) {
	    StringBuffer predName = new StringBuffer("type_of_");
	    predName.append(sortname);
	    predName = this.translatePredicateName(predName);
	    this.typePredicates.put(s, predName);
	}
    }


    /** 
     * Used just to be called from DecProcTranslation
     */
    private final StringBuffer translate(Term term, int skolemization,
	    Vector<QuantifiableVariable> quantifiedVars, Services services)
	    throws IllegalFormulaException {
	return translateTerm(term, quantifiedVars, services);
    }

    private boolean isSomeIntegerSort(Sort s) {
	if (s == jbyteSort || s == jshortSort || s == jintSort
		|| s == jlongSort || s == jcharSort || s == integerSort)
	    return true;
	return false;
    }

}
