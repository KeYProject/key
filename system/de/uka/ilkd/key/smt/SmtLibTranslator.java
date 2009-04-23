package de.uka.ilkd.key.smt;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;

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
	    ArrayList<ArrayList<StringBuffer>> functions,
	    ArrayList<ArrayList<StringBuffer>> predicates,
	    ArrayList<StringBuffer> types, SortHierarchy sortHierarchy) {
	StringBuffer toReturn = new StringBuffer(
		"( benchmark KeY_translation\n");
	// add the sortdeclarations
	// as sortshierarchies are not supported by smt-lib, only one
	// sort should be used
	// no extra sorts needed

	//add the logic definition
	toReturn.append("\n :logic AUFLIA");
	
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
	if (predicates.size() > 0) {
	    toReturn.append("\n:extrapreds (");
	    for (ArrayList<StringBuffer> a : predicates) {
		toReturn.append("(");
		for (StringBuffer s : a) {
		    toReturn.append(s);
		    toReturn.append(" ");
		}
		toReturn.append(") ");
	    }
	    toReturn.append(")");
	}
	
	// add the function declarations
	if (functions.size() > 0) {
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
	    
	for (StringBuffer s : assumptions) {
	    toReturn.append("\n:assumption ").append(s);
	}
	
	// add the formula
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
	return false;
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
	StringBuffer arg;
	if (val < 0) {
	    arg = translateIntegerValue(val * (-1));
	    arg = translateIntegerUnaryMinus(arg);
	} else {
	    arg = new StringBuffer(Long.toString(val));
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

    private StringBuffer makeUnique(StringBuffer name) {
	StringBuffer toReturn = new StringBuffer(name);
	int index;
	// replace array brackets
	index = toReturn.indexOf("[]");
	if (index >= 0) {
	    toReturn.replace(index, index + 2, "_Array");
	} else {
	    index = -1;
	}

	// replace dots brackets
	index = toReturn.indexOf(".");
	if (index >= 0) {
	    toReturn.replace(index, index + 1, "_dot_");
	} else {
	    index = -1;
	}
	
	//replace colons
	index = toReturn.indexOf(":");
	while (index >= 0) {
	    toReturn.replace(index, index + 1, "_");
	    index = toReturn.indexOf(":");
	}
	
	toReturn.append("_").append(counter);
	counter++;
	return toReturn;
    }

}
