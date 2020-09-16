package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class PatternHandler implements SMTHandler {

    public static final Function PATTERN_FUNCTION = makePatternFunction();
    public static final Function FORMULA_PATTERN_FUNCTION = makeFormulaPatternFunction();

    private static final String PATTERN_NAME = "PATTERN";
    private static final String FORMULA_PATTERN_NAME = "FPATTERN";

    private static Function makeFormulaPatternFunction() {
        Sort[] argSorts = { Sort.FORMULA, Sort.FORMULA };
        return new Function(new Name(FORMULA_PATTERN_NAME), Sort.FORMULA, argSorts);
    }

    private static Function makePatternFunction() {
        Sort[] argSorts = { Sort.FORMULA, Sort.ANY };
        return new Function(new Name(PATTERN_NAME), Sort.FORMULA, argSorts);
    }

    @Override
    public void init(MasterHandler masterHandler, Services services) {
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == FORMULA_PATTERN_FUNCTION || op == PATTERN_FUNCTION;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        return SExprs.patternSExpr(trans.translate(term.sub(0)), new SExpr(trans.translate(term.sub(1))));
    }
}
