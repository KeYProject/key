package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

public class UninterpretedSymbolsHandler implements SMTHandler {

    public final static String PREFIX = "ui_";

    @Override
    public void init(Services services) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return (op instanceof Function && term.boundVars().isEmpty())
            || op instanceof ProgramVariable;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();

        // TODO js: should this go in a special literalHandler?
        if (term.sort().name().toString().equals("Null")) {
            return new SExpr("null", Type.UNIVERSE);
        }

        SExpr.Type exprType = term.sort() == Sort.FORMULA ? BOOL : UNIVERSE;
        String sortString = term.sort() == Sort.FORMULA ? "Bool" : "U";

        String name = PREFIX + op.name().toString();
        if(!trans.isKnownSymbol(name)) {
            int a = op.arity();
            SExpr signature = new SExpr(Collections.nCopies(a, new SExpr("U")));
            trans.addDeclaration(
                    new SExpr("declare-fun", new SExpr(name), signature, new SExpr(sortString)));
            trans.addKnownSymbol(name);
            if (op instanceof SortedOperator && term.sort() != Sort.FORMULA) {
                if (op.arity() > 0) {
                    SExpr axiom = funTypeAxiomFromTerm(term, name, trans);
                    trans.addAxiom(axiom);
                }
                if (op.arity() == 0) {
                    SortedOperator sop = (SortedOperator) op;
                    SExpr axiom = new SExpr("assert",
                            new SExpr("instanceof", Type.BOOL, name, SExpr.sortExpr(sop.sort()).toString()));
                    trans.addAxiom(axiom);

                }
            }
        }

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        return new SExpr(name, exprType, children);
    }

    /**
     * Takes a term which represents a function with multiple parameters, and expresses this
     * function along with assertions as to parameter types.
     * "f : int -> boolean" will be translated as a function "ui_f (U) U" along
     * with the assertion that if x is an int, f(x) will be a boolean.
     * @param term the term to translate
     * @param name the name of the function
     * @param master the associated master handler
     * @return the function expression
     */
    private static SExpr funTypeAxiomFromTerm(Term term, String name, MasterHandler master) {
        SortedOperator op = (SortedOperator) term.op();
        List<SExpr> vars_U = new ArrayList<>();
        List<SExpr> vars = new ArrayList<>();
        for (int i = 0; i < op.arity(); ++i) {
            vars_U.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i, Type.NONE, "U"));
            vars.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i));
        }

        List<SExpr> tos = new ArrayList<>();
        int i = 0;
        for (Sort sort : op.argSorts()) {
            master.addSort(sort);
            SExpr var = new SExpr(LogicalVariableHandler.VAR_PREFIX + i);
            tos.add(new SExpr("instanceof", var, SExpr.sortExpr(sort)));
            ++i;
        }
        SExpr ante;
        if (tos.size() == 1) {
            ante = tos.get(0);
        } else {
            ante = new SExpr("and", tos);
        }
        SExpr cons = new SExpr("instanceof", new SExpr(name, vars),
                SExpr.sortExpr(op.sort()));
        SExpr matrix = new SExpr("=>", ante, cons);
        SExpr pattern = SExpr.patternSExpr(matrix, new SExpr(name, vars));
        SExpr axiom = new SExpr("forall", BOOL, new SExpr(vars_U), pattern);
        return new SExpr("assert", axiom);
    }

}
