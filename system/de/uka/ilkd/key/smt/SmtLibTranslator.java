package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.Collection;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

public class SmtLibTranslator extends AbstractSMTTranslator {

    private static final Logger logger = Logger
	    .getLogger(SmtLibTranslator.class.getName());

    // counter used for making names unique
    private int counter = 0;

    private static StringBuffer INTSTRING = new StringBuffer("Int");

    private static StringBuffer FALSESTRING = new StringBuffer("false");

    private static StringBuffer TRUESTRING = new StringBuffer("true");

    private static StringBuffer ALLSTRING = new StringBuffer("forall");

    private static StringBuffer EXISTSTRING = new StringBuffer("exists");

    private static StringBuffer ANDSTRING = new StringBuffer("and");

    private static StringBuffer ORSTRING = new StringBuffer("or");

    private static StringBuffer NOTSTRING = new StringBuffer("not");

    private static StringBuffer EQSTRING = new StringBuffer("=");

    private static StringBuffer IMPLYSTRING = new StringBuffer("implies");

    private static StringBuffer PLUSSTRING = new StringBuffer("+");

    private static StringBuffer MINUSSTRING = new StringBuffer("-");

    private static StringBuffer MULTSTRING = new StringBuffer("*");

    private static StringBuffer LTSTRING = new StringBuffer("<");

    private static StringBuffer GTSTRING = new StringBuffer(">");

    private static StringBuffer LEQSTRING = new StringBuffer("<=");

    private static StringBuffer GEQSTRING = new StringBuffer(">=");

    private static StringBuffer NULLSTRING = new StringBuffer("null");

    private static StringBuffer NULLSORTSTRING = new StringBuffer("NULLSORT");
    
    private static StringBuffer LOGICALIFTHENELSE = new StringBuffer("if_then_else");

    private static StringBuffer TERMIFTHENELSE = new StringBuffer("ite");
    
    private static StringBuffer DISTINCT = new StringBuffer("distinct");
    
    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with
     * 
     * @param sequent
     *                The sequent which shall be translated.
     *                
     * @param services The Services Object belonging to the sequent.
     */
    public SmtLibTranslator(Sequent sequent, Services services) {
	super(sequent, services);
    }

    /**
     * For translating only terms and not complete sequents.
     */
    public SmtLibTranslator(Services s) {
	super(s);
    }

    protected StringBuffer translateNull() {
	return NULLSTRING;
    }

    protected StringBuffer translateNullSort() {
	return NULLSORTSTRING;
    }

    @Override
    protected StringBuffer buildCompleteText(StringBuffer formula,
	    ArrayList<StringBuffer> assumptions,
	    ArrayList<ContextualBlock> assumptionBlocks,
	    ArrayList<ArrayList<StringBuffer>> functions,
	    ArrayList<ArrayList<StringBuffer>> predicates,
	    ArrayList<ContextualBlock> predicateBlocks,
	    ArrayList<StringBuffer> types, SortHierarchy sortHierarchy) {
	StringBuffer toReturn = new StringBuffer(
		"( benchmark KeY_translation\n");
	// add the sortdeclarations
	// as sortshierarchies are not supported by smt-lib, only one
	// sort should be used
	// no extra sorts needed

	String [] commentPredicate = new String[2];
	commentPredicate[ContextualBlock.PREDICATE_FORMULA] = "\n\n:notes \"Predicates used in formula:\"";
	commentPredicate[ContextualBlock.PREDICATE_TYPE]    = "\n\n:notes \"Types expressed by predicates:\"";
	String [] commentAssumption = new String[5];
	commentAssumption[ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION] = "\n\n:notes \"Assumptions for dummy variables:\"";
	commentAssumption[ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION] = "\n\n:notes \"Assumptions for function definitions:\""; 
	commentAssumption[ContextualBlock.ASSUMPTION_SORT_PREDICATES] = "\n\n:notes \"Assumptions for sort predicates:\"";
	commentAssumption[ContextualBlock.ASSUMPTION_TYPE_HIERARCHY] = "\n\n:notes \"Assumptions for type hierarchy:\"";
	commentAssumption[ContextualBlock.ASSUMPTION_TACLET_TRANSLATION]= "\n\n:notes \"Assumptions for taclets:\"";
	
	//add the logic definition
	toReturn.append("\n:logic AUFLIA");
	
	// add the sort declarations
	StringBuffer extrasorts = new StringBuffer();	    
	for (StringBuffer s : types) {
	    if (!(s == INTSTRING || s.equals(INTSTRING))) {
		extrasorts.append(s);
		extrasorts.append(" ");
	    }
	}
	if (extrasorts.length() > 0) {
	    toReturn.append("\n :extrasorts (");
	    toReturn.append(extrasorts);
	    toReturn.append(")");
	}

	// add the predicate declarations
	// add the predicate declarations for formula predicates
	ArrayList<ArrayList<StringBuffer>> PredicatesToRemove = new ArrayList<ArrayList<StringBuffer>>();
	
	StringBuffer preds = new StringBuffer();
	
	for(int k=0; k < commentPredicate.length; k++){
		ContextualBlock block = predicateBlocks.get(k);
		
		
		if (block.getStart() <= block.getEnd()) {
		    preds.append(commentPredicate[block.getType()]);
		    preds.append("\n:extrapreds (");
		    for (int i = block.getStart(); i <= block.getEnd(); i++) {
			preds.append("(");
			PredicatesToRemove.add(predicates.get(i));
			for (StringBuffer s : predicates.get(i)) {
			    preds.append(s);
			    preds.append(" ");
			}
			preds.append(") ");
		    }
		    preds.append(")");
		}
	}

	

	predicates.removeAll(PredicatesToRemove);
	
	// add other predicates
	if (predicates.size() > 0) {
	    preds = preds.append("\n\n:notes \"Other predicates\"");
	    preds.append("\n:extrapreds (");
	    for (ArrayList<StringBuffer> a : predicates) {
		preds.append("(");
		for (StringBuffer s : a) {
		    preds.append(s);
		    preds.append(" ");
		}
		preds.append(") ");
	    }
	    preds.append(")");
	}
	
	toReturn.append(preds);
	
	// add the function declarations
	if (functions.size() > 0) {
	    toReturn.append("\n\n:notes \"Function declarations\""); 
	    toReturn.append("\n:extrafuns (");
	    for (ArrayList<StringBuffer> a : functions) {
		toReturn.append("(");
		for (StringBuffer s : a) {
		    toReturn.append(s);
		    toReturn.append(" ");
		}
		toReturn.append(") ");
	    }
	    toReturn.append(")");
	}
	    
	//add the assumptions
	ArrayList<StringBuffer> AssumptionsToRemove = new ArrayList<StringBuffer>();
	    StringBuffer assump = new StringBuffer();	
	
	for(int k=0; k < commentAssumption.length; k++){
	    ContextualBlock block = assumptionBlocks.get(k);
	
	    if (block.getStart() <= block.getEnd()) {
		assump.append(commentAssumption[block.getType()]);
	    	    for(int i=block.getStart(); i <= block.getEnd(); i++){
	    		AssumptionsToRemove.add(assumptions.get(i));   
	    		assump.append("\n:assumption ").append(assumptions.get(i)); 
	    	    }
		}  
	}
	    
	

	
	
	
	assumptions.removeAll(AssumptionsToRemove);
	
	
	
	if (assumptions.size() > 0) {
	    assump.append("\n\n:notes \"Other assumptions:\"");    
	    for (StringBuffer s : assumptions) {
		assump.append("\n:assumption ").append(s);
	    }
	}
	
	toReturn.append(assump);
	
	// add the formula
	toReturn.append("\n\n:notes \"The formula to proof:\""); 
	formula = this.translateLogicalNot(formula);
	toReturn.append("\n:formula ").append(formula).append("\n");

	toReturn.append(")");
	logger.info("Resulting formula after translation:");
	logger.info(toReturn);
	return toReturn;

    }

    /**
     * Translate a sort.
     * 
     * @param name
     *                the sorts name
     * @param isIntVal
     *                true, if the sort should represent some kind of
     *                integer
     * 
     * @return Argument 1 of the return value is the sort used in var
     *         declarations, Argument2 is the sort used for type predicates
     */
    protected StringBuffer translateSort(String name, boolean isIntVal) {
	StringBuffer uniqueName = makeUnique(new StringBuffer(name));
	return uniqueName;
    }

    @Override
    protected boolean isMultiSorted() {
	return true;
    }

    @Override
    protected StringBuffer getIntegerSort() {
	return INTSTRING;
    }

    @Override
    protected StringBuffer translateFunction(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	return buildFunction(name, args);
    }

    @Override
    protected StringBuffer translateFunctionName(StringBuffer name) {
	return makeUnique(name);
    }

    @Override
    protected StringBuffer translateIntegerDiv(StringBuffer arg1,
	    StringBuffer arg2) {
	return new StringBuffer("unknownOp");
    }

    @Override
    protected StringBuffer translateIntegerGeq(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(GEQSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerGt(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(GTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerLeq(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(LEQSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerLt(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(LTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerMinus(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerMod(StringBuffer arg1,
	    StringBuffer arg2) {
	return new StringBuffer("unknownOp");
    }

    @Override
    protected StringBuffer translateIntegerMult(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(MULTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerPlus(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(PLUSSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerUnaryMinus(StringBuffer arg) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	StringBuffer n = new StringBuffer("0");
	args.add(n);
	args.add(arg);
	return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerValue(long val) {
	
	StringBuffer arg =  new StringBuffer(Long.toString(val));
	
	if(val < 0){
	   // delete the minus sign. 
	   arg = new StringBuffer(arg.substring(1, arg.length()));  
	   arg = translateIntegerUnaryMinus(arg);
	}
	
	return arg;	
    }

    @Override
    protected StringBuffer translateLogicalConstant(StringBuffer name) {
	return makeUnique(name);
    }

    @Override
    protected StringBuffer translateLogicalVar(StringBuffer name) {
	StringBuffer toReturn = (new StringBuffer("?"))
		.append(makeUnique(name));
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalAll(StringBuffer var,
	    StringBuffer type, StringBuffer form) {
	StringBuffer toReturn = new StringBuffer();
	toReturn.append("(");
	toReturn.append(ALLSTRING);

	toReturn.append(" (");
	toReturn.append(var);
	toReturn.append(" ");
	toReturn.append(type);
	toReturn.append(") ");

	toReturn.append(form);

	toReturn.append(")");
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalAnd(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(ANDSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalEquivalence(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);

	ArrayList<StringBuffer> argsrev = new ArrayList<StringBuffer>();
	argsrev.add(arg2);
	argsrev.add(arg1);

	ArrayList<StringBuffer> forms = new ArrayList<StringBuffer>();
	forms.add(buildFunction(IMPLYSTRING, args));
	forms.add(buildFunction(IMPLYSTRING, argsrev));
	return buildFunction(ANDSTRING, forms);
    }

    @Override
    protected StringBuffer translateLogicalExist(StringBuffer var,
	    StringBuffer type, StringBuffer form) {
	StringBuffer toReturn = new StringBuffer();
	toReturn.append("(");
	toReturn.append(EXISTSTRING);

	toReturn.append("(");
	toReturn.append(var);
	toReturn.append(" ");
	toReturn.append(type);
	toReturn.append(")");

	toReturn.append(form);

	toReturn.append(")");
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalFalse() {
	return new StringBuffer(FALSESTRING);
    }

    @Override
    protected StringBuffer translateLogicalImply(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(IMPLYSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalNot(StringBuffer arg) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg);
	return buildFunction(NOTSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalOr(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(ORSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalTrue() {
	return new StringBuffer(TRUESTRING);
    }

    @Override
    protected StringBuffer translateObjectEqual(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return buildFunction(EQSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalIfThenElse(StringBuffer cond, StringBuffer ifterm, StringBuffer elseterm) {
        ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
        args.add(cond);
        args.add(ifterm);
        args.add(elseterm);
        return buildFunction(LOGICALIFTHENELSE, args);
    }
    
    @Override
    protected StringBuffer translateTermIfThenElse(StringBuffer cond, StringBuffer ifterm, StringBuffer elseterm) throws IllegalFormulaException {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
        args.add(cond);
        args.add(ifterm);
        args.add(elseterm);
        return buildFunction(TERMIFTHENELSE, args);
    }
    
    @Override
    protected StringBuffer translatePredicate(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	return buildFunction(name, args);
    }

    @Override
    protected StringBuffer translatePredicateName(StringBuffer name) {
	return makeUnique(name);
    }
    
    
    private boolean haveSameArgs(ImmutableArray<Sort> list1, ImmutableArray<Sort> list2){
	if(list1.size() == list2.size())
	for(int i=0; i < list1.size(); i++){
	    if(!list1.get(i).equals(list2.get(i))){
		return false;
	    }
	}
	return true;
    }
    
    private boolean haveSameSortSignature(FunctionWrapper fw1, FunctionWrapper fw2){
	Function f1 = fw1.getFunction();
	Function f2 = fw2.getFunction();
	if(!fw1.getName().equals(fw2.getName()) && 
	   f1.sort().equals(f2.sort()) &&
	   haveSameArgs(f1.argSorts(),f2.argSorts())){
	   return true;
	}
	return false;
    }
    
    private StringBuffer getQuantifiedVariable(int pos){
	return new StringBuffer("?n"+pos);
    }
    
    private ArrayList<StringBuffer> getQuantifiedVariables(int count, int start){
	ArrayList<StringBuffer> list = new ArrayList<StringBuffer>();
	for(int i=0; i < count; i++){
	    list.add(getQuantifiedVariable(i+start));
	}
	return list;
    }
    

   
    protected StringBuffer buildDistinct(FunctionWrapper [] fw){
	int start =0;
	ArrayList<StringBuffer> temp []=  new ArrayList[fw.length];
	
	
	StringBuffer rightSide = new StringBuffer();
	rightSide.append("( "+ DISTINCT + " ");
	for(int i=0; i < fw.length; i++){
		temp[i] = getQuantifiedVariables(fw[i].getFunction().arity(),start);
		start += fw[i].getFunction().arity();
		rightSide.append(buildFunction(fw[i].getName(),temp[i])+" ");
    
	}
	
	rightSide.append(")");
	
	for(int j=0; j < fw.length; j++){
	    for(int i=0; i < fw[j].getFunction().arity(); i++){
		      Sort sort = fw[j].getFunction().argSorts().get(i);
		      rightSide = translateLogicalAll(temp[j].get(i),usedDisplaySort.get(sort),rightSide);
		     
		 }
		   
	}
	
	
	return rightSide;
	
    }
    protected StringBuffer translateUniqueness(FunctionWrapper function,
            Collection<FunctionWrapper> distinct) throws IllegalFormulaException {
	if(!function.getFunction().isUnique()){
	    return null;
	}
	function.setUsedForUnique(true);
	
	StringBuffer result = translateLogicalTrue();
	for(FunctionWrapper fw : distinct){
	    if(!fw.isUsedForUnique() &&
	        fw.getFunction().isUnique()){
		FunctionWrapper array [] = {function, fw};
	       result = translateLogicalAnd(result, buildDistinct(array));
		
		
	    }
	}
	return result;
    }
    


    private StringBuffer buildFunction(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	StringBuffer toReturn = new StringBuffer();
	if (args.size() == 0) {
	    toReturn.append(name);
	} else {
	    toReturn.append("(");
	    toReturn.append(name);
	    for (int i = 0; i < args.size(); i++) {
		toReturn.append(" ");
		toReturn.append(args.get(i));
	    }
	    toReturn.append(")");
	}
	return toReturn;
    }

    private StringBuffer removeIllegalChars(StringBuffer template, ArrayList<String> toReplace, ArrayList<String> replacement) {
	//replace one String
	for (int i = 0; i < toReplace.size(); i++) {
	    String toRep = toReplace.get(i);
	    String replace = replacement.get(i);
	    int index = template.indexOf(toRep);
	    while (index >= 0) {
		template.replace(index, index + toRep.length(), replace);
		index = template.indexOf(toRep);
	    }
	}
	
	return template;
    }
    
    
    
    private StringBuffer makeUnique(StringBuffer name) {
	StringBuffer toReturn = new StringBuffer(name);
	
	//build the replacement pairs
	ArrayList<String> toReplace = new ArrayList<String>();
	ArrayList<String> replacement = new ArrayList<String>();
	
	toReplace.add("[]");
	replacement.add("_Array");
	
	toReplace.add("<");
	replacement.add("_abo_");
	
	toReplace.add(">");
	replacement.add("_abc_");
	
	toReplace.add("{");
	replacement.add("_cbo_");
	
	toReplace.add("}");
	replacement.add("_cbc_");
	
	toReplace.add(".");
	replacement.add("_dot_");
	
	toReplace.add(":");
	replacement.add("_col_");
	
	toReplace.add("\\");
	replacement.add("_");
	
	toReplace.add("$");
	replacement.add("_dollar_");
	
	toReturn = this.removeIllegalChars(toReturn, toReplace, replacement);
	// names are must not begin with special characters
	toReturn = (new StringBuffer()).append("a").append(toReturn);
	
	toReturn.append("_").append(counter);
	counter++;
	return toReturn;
    }

}
