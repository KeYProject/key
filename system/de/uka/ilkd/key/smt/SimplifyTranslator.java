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

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;

public class SimplifyTranslator extends AbstractSMTTranslator {

    private static final Logger logger = Logger
    .getLogger(SimplifyTranslator.class.getName());
    
//  counter used for making names unique
    private int counter = 0;

    private static StringBuffer INTSTRING = new StringBuffer("int");

    private static StringBuffer FALSESTRING = new StringBuffer("FALSE");

    private static StringBuffer TRUESTRING = new StringBuffer("TRUE");

    private static StringBuffer ALLSTRING = new StringBuffer("FORALL");

    private static StringBuffer EXISTSTRING = new StringBuffer("EXISTS");

    private static StringBuffer ANDSTRING = new StringBuffer("AND");

    private static StringBuffer ORSTRING = new StringBuffer("OR");

    private static StringBuffer NOTSTRING = new StringBuffer("NOT");

    private static StringBuffer EQSTRING = new StringBuffer("EQ");

    private static StringBuffer IMPLYSTRING = new StringBuffer("IMPLIES");

    private static StringBuffer PLUSSTRING = new StringBuffer("+");

    private static StringBuffer MINUSSTRING = new StringBuffer("-");

    private static StringBuffer MULTSTRING = new StringBuffer("*");

    private static StringBuffer LTSTRING = new StringBuffer("<");

    private static StringBuffer GTSTRING = new StringBuffer(">");

    private static StringBuffer LEQSTRING = new StringBuffer("<=");

    private static StringBuffer GEQSTRING = new StringBuffer(">=");

    private static StringBuffer NULLSTRING = new StringBuffer("null");

    private static StringBuffer NULLSORTSTRING = new StringBuffer("NULLSORT");
    
    
    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with
     * 
     * @param sequent
     *                The sequent which shall be translated.
     *                
     * @param services
     * 		      The services Object belonging to the sequent.
     */
    public SimplifyTranslator(Sequent sequent, Services services) {
	super(sequent, services);
    }
    
    public SimplifyTranslator(Services services) {
	super(services);
    }
    
    @Override
    protected StringBuffer buildCompleteText(StringBuffer formula,
	    ArrayList<StringBuffer> assumptions,
	    ArrayList<ArrayList<StringBuffer>> functions,
	    ArrayList<ArrayList<StringBuffer>> predicates,
	    ArrayList<StringBuffer> types, SortHierarchy sortHirarchy) {
	
	StringBuffer toReturn = new StringBuffer();
	
	for (ArrayList<StringBuffer> s : predicates) {
	    toReturn.append("(DEFPRED (" + s.get(0));
	    for (int i = 1; i < s.size(); i++) {
		StringBuffer var = new StringBuffer("x");
		var = this.makeUnique(var);
		toReturn.append(" " + var);
	    }
	    toReturn.append("))\n");
	}
	
	if (assumptions.size() > 0) {
	    StringBuffer ass = assumptions.get(0);
	    for (int i = 1; i < assumptions.size(); i++) {
		ass = this.translateLogicalAnd(ass, assumptions.get(i));
	    }
	    formula = this.translateLogicalImply(ass, formula);
	}
	
	/* CAUTION!! For some reason, the solver gives the correct result,
	 * if this part is added. The reason, why this is, is not clear ro me yet!
	 */
	StringBuffer temp = new StringBuffer ();
	temp.append("(").append(ALLSTRING).append(" () (").append(EXISTSTRING)
		.append(" () ").append(formula).append("))");
	formula = temp;
	/* End of adding part */
	
	toReturn.append(formula);
	
	logger.info("Resulting formula after translation:");
	logger.info(toReturn);
	
	return toReturn;
    }

    @Override
    protected StringBuffer getIntegerSort() {
	return INTSTRING;
    }

    @Override
    protected boolean isMultiSorted() {
	return false;
    }

    @Override
    protected StringBuffer translateFunction(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	return this.buildFunction(name, args);
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
	return this.buildFunction(GEQSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerGt(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(GTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerLeq(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(LEQSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerLt(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(LTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerMinus(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(MINUSSTRING, args);
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
	return this.buildFunction(MULTSTRING, args);
    }

    @Override
    protected StringBuffer translateIntegerPlus(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(PLUSSTRING, args);
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
	return new StringBuffer(""+val);
    }

    @Override
    protected StringBuffer translateLogicalAll(StringBuffer var,
	    StringBuffer type, StringBuffer form) {
	StringBuffer toReturn = new StringBuffer("(" + ALLSTRING + " ");
	toReturn.append("(" + var + ") " + form + ")");
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalAnd(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(ANDSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalConstant(StringBuffer name) {
	return makeUnique(name);
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
	StringBuffer toReturn = new StringBuffer("(" + EXISTSTRING + " ");
	toReturn.append("(" + var + ") " + form + ")");
	return toReturn;
    }

    @Override
    protected StringBuffer translateLogicalFalse() {
	return FALSESTRING;
    }

    @Override
    protected StringBuffer translateLogicalImply(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(IMPLYSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalNot(StringBuffer arg) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg);
	return this.buildFunction(NOTSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalOr(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(ORSTRING, args);
    }

    @Override
    protected StringBuffer translateLogicalTrue() {
	return TRUESTRING;
    }

    @Override
    protected StringBuffer translateLogicalVar(StringBuffer name) {
	return makeUnique(name);
    }

    @Override
    protected StringBuffer translateNull() {
	return NULLSTRING;
    }

    @Override
    protected StringBuffer translateNullSort() {
	return NULLSORTSTRING;
    }

    @Override
    protected StringBuffer translateLogicalIfThenElse(StringBuffer cond, StringBuffer ifterm, StringBuffer elseterm) {
        StringBuffer toReturn = this.translateLogicalImply(cond, ifterm);
        StringBuffer temp = this.translateLogicalNot(cond);
        temp = this.translateLogicalImply(temp, elseterm);
        toReturn = this.translateLogicalAnd(toReturn, temp);
        return toReturn;
    }
    
    @Override
    protected StringBuffer translateObjectEqual(StringBuffer arg1,
	    StringBuffer arg2) {
	ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
	args.add(arg1);
	args.add(arg2);
	return this.buildFunction(EQSTRING, args);
    }

    @Override
    protected StringBuffer translatePredicate(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	return this.buildFunction(name, args);
    }

    @Override
    protected StringBuffer translatePredicateName(StringBuffer name) {
	return makeUnique(name);
    }

    @Override
    protected StringBuffer translateSort(String name, boolean isIntVal) {
	return makeUnique(new StringBuffer(name));
    }

    private StringBuffer buildFunction(StringBuffer name,
	    ArrayList<StringBuffer> args) {
	StringBuffer toReturn = new StringBuffer();
	    toReturn.append("(");
	    toReturn.append(name);
	    for (int i = 0; i < args.size(); i++) {
		toReturn.append(" ");
		toReturn.append(args.get(i));
	    }
	    toReturn.append(")");
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
