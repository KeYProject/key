package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

/**
 * A collection of static methods that {@link SMTHandler}s are likely to use.
 *
 * @author Mattias Ulbrich
 * @author Jonas Schiffl
 */
public class HandlerUtil {

    private HandlerUtil() {
        throw new Error("do not instantiate");
    }

    /**
     * Generate a smtlib expression for the smtlib declaration that
     * represents the operator op.
     *
     * @param op the operator to be declared in smtlib
     * @param name the name to use on the smt lib side.
     * @return an SExpr of type {@code (declare-fun ...)}
     */
    public static SExpr funDeclaration(SortedOperator op, String name) {
        String sortString = op.sort() == Sort.FORMULA ? "Bool" : "U";
        SExpr signature = new SExpr(Collections.nCopies(op.arity(), new SExpr("U")));
        return new SExpr("declare-fun", new SExpr(name), signature, new SExpr(sortString));
    }

    /**
     * Takes a term which represents a function with multiple parameters, and expresses this
     * function along with assertions as to parameter types.
     * "f : int -> boolean" will be translated as a function "ui_f (U) U" along
     * with the assertion that if x is an int, f(x) will be a boolean.
     * @param op the operator to translate
     * @param name the name of the function
     * @param master the associated master handler
     * @return the function expression
     */
    static SExpr funTypeAxiom(SortedOperator op, String name, MasterHandler master) throws SMTTranslationException {
        return funTypeAxiom(name, op.arity(), op.sort(), master);
    }

    /**
     * Takes a term which represents a function with multiple parameters, and expresses this
     * function along with assertions as to parameter types.
     * "f : int -> boolean" will be translated as a function "ui_f (U) U" along
     * with the assertion that if x is an int, f(x) will be a boolean.
     * @param name the name of the function
     * @param arity the number of parameters that the function accepts
     * @param sort the result type of the function
     * @param master the associated master handler
     * @return the function expression
     */
    static SExpr funTypeAxiom(String name, int arity, Sort sort, MasterHandler master) throws SMTTranslationException {
        List<SExpr> vars_U = new ArrayList<>();
        List<SExpr> vars = new ArrayList<>();
        for (int i = 0; i < arity; ++i) {
            vars_U.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i, Type.NONE, "U"));
            vars.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i));
        }

        List<SExpr> tos = new ArrayList<>();
//        int i = 0;
//        for (Sort sort : op.argSorts()) {
//            // TODO MU: are these restrictions actually needed?
//            // It is way simpler to leave them out. Still sound? I assume so ...
//            master.addSort(sort);
//            SExpr var = new SExpr(LogicalVariableHandler.VAR_PREFIX + i);
//            tos.add(SExprs.instanceOf(var, SExprs.sortExpr(sort)));
//            ++i;
//        }

        SExpr ante = SExprs.and(tos);
        master.addSort(sort);
        SExpr cons = SExprs.instanceOf(new SExpr(name, vars),
                SExprs.sortExpr(sort));
        SExpr matrix = SExprs.imp(ante, cons);
        SExpr pattern = SExprs.patternSExpr(matrix, new SExpr(name, vars));
        SExpr axiom = SExprs.forall(vars_U, pattern);
        return SExprs.assertion(axiom);
    }


}
