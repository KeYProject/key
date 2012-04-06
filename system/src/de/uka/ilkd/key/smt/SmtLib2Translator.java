// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.util.ArrayList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.sort.Sort;


public class SmtLib2Translator extends AbstractSMTTranslator {



	// counter used for making names unique
    private int counter = 0;

    private static StringBuffer INTSTRING = new StringBuffer("Int");
    
    private static final StringBuffer BOOL = new StringBuffer("Bool");

	private static final String GAP = "          ";

    private static StringBuffer FALSESTRING = new StringBuffer("false");

    private static StringBuffer TRUESTRING = new StringBuffer("true");

    private static StringBuffer ALLSTRING = new StringBuffer("forall");

    private static StringBuffer EXISTSTRING = new StringBuffer("exists");

    private static StringBuffer ANDSTRING = new StringBuffer("and");

    private static StringBuffer ORSTRING = new StringBuffer("or");

    private static StringBuffer NOTSTRING = new StringBuffer("not");

    private static StringBuffer EQSTRING = new StringBuffer("=");

    private static StringBuffer IMPLYSTRING = new StringBuffer("=>");

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
    public SmtLib2Translator(Sequent sequent, Services services, Configuration config) {
	super(sequent, services,config);
    }

    /**
     * For translating only terms and not complete sequents.
     */
    public SmtLib2Translator(Services s,Configuration config) {
	super(s,config);
    }

    protected StringBuffer translateNull() {
	return NULLSTRING;
    }
    
    @Override
    protected StringBuffer getNullName() {
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
    	    ArrayList<StringBuffer> types, SortHierarchy sortHierarchy,
    	    SMTSettings settings){
    	StringBuffer result = new StringBuffer("(set-logic");
    	result.append(" "+settings.getLogic() +" )\n");
    	result.append("(set-option :print-success true) \n");
    	result.append("(set-option :produce-unsat-cores true)\n");
    	result.append("(set-option :produce-models true)\n");
    	result.append("(set-option :produce-proofs true)\n");
    	
    
    	createSortDeclaration(types, result);
    	createFunctionDeclarations(result, predicates, predicateBlocks,functions);
    	StringBuffer assump = createAssumptions(assumptions, assumptionBlocks);
    	
    	result.append("(assert(not \n");
    	if(assump.length() >0){
    		result.append("(=> ").append(assump);    		
    	}
    	result.append("\n\n"+GAP+"; The formula to be proved:\n\n"); 
    	
    	result.append(formula);
    	
    	if(assump.length()>0){
    		result.append("\n)"+GAP +"; End of imply.");
    	}
    	result.append("\n))"+GAP+"; End of assert.");
    	result.append("\n\n(check-sat)");

    	
    	return result.append("\n"+GAP+"; end of smt problem declaration");
    }
    
    private StringBuffer createAssumptions( ArrayList<StringBuffer> assumptions,
    	    ArrayList<ContextualBlock> assumptionBlocks){
    	String [] commentAssumption = new String[8];
    	commentAssumption[ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION] = "Assumptions for dummy variables:";
    	commentAssumption[ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION] = "Assumptions for function definitions:"; 
    	commentAssumption[ContextualBlock.ASSUMPTION_SORT_PREDICATES] = "Assumptions for sort predicates:";
    	commentAssumption[ContextualBlock.ASSUMPTION_TYPE_HIERARCHY] = "Assumptions for type hierarchy:";
    	commentAssumption[ContextualBlock.ASSUMPTION_TACLET_TRANSLATION]= "Assumptions for taclets:";
    	commentAssumption[ContextualBlock.ASSUMPTION_DISTINCT]= "Assumptions for uniqueness of functions:";
    	commentAssumption[ContextualBlock.ASSUMPTION_INTEGER]= "Assumptions for very small and very big integers:";
    	commentAssumption[ContextualBlock.ASSUMPTION_MULTIPLICATION]= "Assumptions for uninterpreted multiplication:";
    	
    	//add the assumptions
    	ArrayList<StringBuffer> AssumptionsToRemove = new ArrayList<StringBuffer>();
    	    StringBuffer assump = new StringBuffer();	
    	boolean needsAnd = assumptions.size() > 1;
    	
    	for(int k=0; k < commentAssumption.length; k++){
    	    ContextualBlock block = assumptionBlocks.get(k);
    	
    	    if (block.getStart() <= block.getEnd()) {
    	   	    assump.append("\n"+GAP+"; "+commentAssumption[block.getType()]+"\n");    
    	    	    for(int i=block.getStart(); i <= block.getEnd(); i++){
    	    		AssumptionsToRemove.add(assumptions.get(i));   
    	    		assump.append(assumptions.get(i));
    	    		assump.append("\n");
    	    	    }
    		}  
    	}
    	    
    	

    	
    	
    	
    	assumptions.removeAll(AssumptionsToRemove);
    	
    	
    	
    	if (assumptions.size() > 0) {
    	    assump.append("\n"+GAP+"; Other assumptions:\n");    
    	    for (StringBuffer s : assumptions) {
    			assump.append(s).append("\n"); 
    	    }
    	}
    	StringBuffer result = new StringBuffer();
    	if(needsAnd){
    		result.append("(and\n");
    		result.append(assump);
    		result.append("\n)"+GAP+"; End of assumptions.\n");
    		
    	}
    	return result;
    }
    
    private void createFunctionDeclarations(StringBuffer result,
    	    ArrayList<ArrayList<StringBuffer>> predicates,
    	    ArrayList<ContextualBlock> predicateBlocks,
    	    ArrayList<ArrayList<StringBuffer>> functions){
    	StringBuffer temp = new StringBuffer();
    	createPredicateDeclaration(temp, predicates, predicateBlocks);
    	createFunctionDeclaration(temp,functions);
    	if(temp.length() > 0){
    		//result.append("\n:funs(");
    		result.append(temp);
    		//result.append("\n)"+GAP+"; end of function declaration \n");
        	
    	}
    }
    
    private void createFunctionDeclaration(StringBuffer result,   ArrayList<ArrayList<StringBuffer>>  functions){
    	// add the function declarations
    	if (functions.size() > 0) {
    	    result.append(translateComment(1,"Function declarations\n")); 
    	    for (ArrayList<StringBuffer> function : functions) {
    	    	createFunctionDeclaration(function, false, result);
    	    }
    	}
    }
    
    private void createPredicateDeclaration(StringBuffer result,
    	    ArrayList<ArrayList<StringBuffer>> predicates,
    	    ArrayList<ContextualBlock> predicateBlocks){
    	String [] commentPredicate = new String[2];
    	commentPredicate[ContextualBlock.PREDICATE_FORMULA] = "Predicates used in formula:\n";
    	commentPredicate[ContextualBlock.PREDICATE_TYPE]    = "Types expressed by predicates:\n";
    	
    	ArrayList<ArrayList<StringBuffer>> PredicatesToRemove = new ArrayList<ArrayList<StringBuffer>>();

    	StringBuffer temp = new StringBuffer();
    	
    	for(int k=0; k < commentPredicate.length; k++){
    		ContextualBlock block = predicateBlocks.get(k);
    		
    		
    		if (block.getStart() <= block.getEnd()) {
    			temp.append(translateComment(0,commentPredicate[block.getType()]+"\n"));
    		    
    		    for (int i = block.getStart(); i <= block.getEnd(); i++) {
    		    	PredicatesToRemove.add(predicates.get(i));
    		    	createFunctionDeclaration(predicates.get(i),true, temp);
    		    }
    		    
    		}
    	}    	

    	predicates.removeAll(PredicatesToRemove);
    	
    	// add other predicates
    	if (predicates.size() > 0) {
    		temp.append(translateComment(1,"Other predicates\n"));
     	    for (ArrayList<StringBuffer> predicate : predicates) {
     	    	createFunctionDeclaration(predicate,true, temp);
    	    }
    	}
    	
    	if(temp.length()>0){
    		result.append(temp);
    	}
    	

    }
    
    private void createFunctionDeclaration(ArrayList<StringBuffer> function,boolean isPredicate, StringBuffer result) {
		result.append("(declare-fun ");
		StringBuffer name = function.remove(0);
		StringBuffer returnType = isPredicate ? BOOL : function.remove(function.size()-1);
		result.append(name);
		result.append(" (");
		for (StringBuffer s : function) {
		    result.append(s);
		    result.append(" ");
		}
		result.append(") ");
		result.append(returnType);
		result.append(" )\n");	
    }
    
    private void createSortDeclaration(ArrayList<StringBuffer> types, StringBuffer result){
    	result.append("\n"+GAP+"; Declaration of sorts.\n");
    	for(StringBuffer type : types){
    		if (!(type == INTSTRING || type.equals(INTSTRING))){
    			createSortDeclaration(type,result);
    		}
    	}
    //	if(temp.length() > 0){
    	//	result.append("\n:sorts (");
    	//	result.append(temp);
    	//	result.append(")\n");
    	//}
    	
    }
    
    private void createSortDeclaration(StringBuffer type, StringBuffer result){
    	result.append("(declare-sort "+type+" 0)\n");
    	
    	
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
	StringBuffer toReturn = (new StringBuffer(""))
		.append(makeUnique(name));
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalAll(StringBuffer var,
	    StringBuffer type, StringBuffer form) {
	StringBuffer toReturn = new StringBuffer();
	toReturn.append("(");
	toReturn.append(ALLSTRING);

	toReturn.append(" ((");
	toReturn.append(var);
	toReturn.append(" ");
	toReturn.append(type);
	toReturn.append(")) ");

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

	toReturn.append("((");
	toReturn.append(var);
	toReturn.append(" ");
	toReturn.append(type);
	toReturn.append("))");

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
    
    
 



    @Override
    protected StringBuffer translateDistinct(FunctionWrapper [] fw){
	if(getSettings() == null || !getSettings().useBuiltInUniqueness()){
	    return super.translateDistinct(fw);
	}
	int start =0;
	ArrayList<ArrayList<StringBuffer>> temp = new ArrayList<ArrayList<StringBuffer>>();
	
	StringBuffer rightSide = new StringBuffer();
	rightSide.append("( "+ DISTINCT + " ");
	for(int i=0; i < fw.length; i++){
		temp.add(createGenericVariables(fw[i].getFunction().arity(),start));
		start += fw[i].getFunction().arity();
		rightSide.append(buildFunction(fw[i].getName(),temp.get(i))+" ");
    
	}
	
	rightSide.append(")");
	
	for(int j=0; j < fw.length; j++){
	    for(int i=0; i < fw[j].getFunction().arity(); i++){
		      Sort sort = fw[j].getFunction().argSorts().get(i);
		      rightSide = translateLogicalAll(temp.get(j).get(i),usedDisplaySort.get(sort),rightSide);
		     
		 }		   
	}	
	return rightSide;
	
    }

    private StringBuffer buildFunction(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	StringBuffer toReturn = new StringBuffer();
	if (args.size() == 0) {
	    toReturn.append(name);
	} else {
	    toReturn.append("(");
	    toReturn.append(name+" ");
    	
	    for (int i = 0; i < args.size(); i++) {
		toReturn.append(args.get(i)+" ");
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
    
    
    
    protected StringBuffer translateComment(int newLines, String comment){
    	StringBuffer buffer = new StringBuffer();
    	for(int i=0; i < newLines; i++){
    		buffer.append("\n");
    	}
    	return buffer.append( GAP+"; "+ comment);
    }


}
