/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This class is a collection of static functions to construct SExpr objects.
 *
 * @author Mattias Ulbrich
 */
public class SExprs {

    private SExprs() {
        throw new Error("do not instantiate");
    }

    /**
     * The string prefix used for sort names in SMT,
     */
    public static final String SORT_PREFIX = "sort_";

    /**
     * The constant "true" of type Bool
     */
    public static final SExpr TRUE = new SExpr("true", Type.BOOL);

    /**
     * The constant "false" of type Bool
     */
    public static final SExpr FALSE = new SExpr("false", Type.BOOL);

    /**
     * The constant "0" of type Int
     */
    public static final SExpr ZERO = new SExpr("0", IntegerOpHandler.INT);

    /**
     * Produce a conjunction of SExprs.
     *
     * There is some optimisation regarding the nature of the list of expressions: If it is empty,
     * the result is "true". If it is a singleton, it is this single expression.
     *
     * @param clauses non-null list of boolean expression
     * @return an SExpr equivalent to the conjunction of the clauses.
     */
    public static SExpr and(List<SExpr> clauses) {
        switch (clauses.size()) {
        case 0:
            return TRUE;
        case 1:
            return clauses.get(0);
        default:
            return new SExpr("and", Type.BOOL, clauses);
        }
    }

    /**
     * Produce an implication from an assumption and a conclusion.
     * <p>
     * There is some optimisation if there are constants involved.
     * <p>
     * If the assumption is false, the result is true. If the assumption is true, the result is the
     * conclusion. If the conclusion is true, the result is true. If the conclusion is false, the
     * result is the negation of the assumption.
     *
     * @param ante a boolean expression
     * @param cons a boolean expression
     * @return a boolean expression equivalent to the implication {@code (=> ante concl)}
     */
    public static SExpr imp(SExpr ante, SExpr cons) {
        if (ante.equals(TRUE)) {
            return cons;
        }
        if (cons.equals(FALSE)) {
            return not(ante);
        }
        if (ante.equals(FALSE) || cons.equals(TRUE)) {
            return TRUE;
        }
        return new SExpr("=>", Type.BOOL, ante, cons);
    }

    /**
     * Produce a logical negation
     *
     * @param se a boolean expression
     * @return a boolean expresion
     */
    private static SExpr not(SExpr se) {
        return new SExpr("not", Type.BOOL, se);
    }

    /**
     * Produce a universal quantification.
     *
     * If vars is empty: no quantifiers are produced and if the matrix has a pattern, the pattern is
     * removed.
     *
     * @param vars a list of variable declarations {@code (var Type)}
     * @param matrix a boolean expression
     * @return
     */
    public static SExpr forall(List<SExpr> vars, SExpr matrix) throws SMTTranslationException {
        if (vars.isEmpty()) {
            if (matrix.getName().equals("!")) {
                return matrix.getChildren().get(0);
            }
            return matrix;
        } else {
            return new SExpr("forall", Type.BOOL, new SExpr(vars), coerce(matrix, Type.BOOL));
        }
    }

    /**
     * Takes an SExpression and converts it to the given type, if possible.
     *
     * @param exp the SExpression to convert
     * @param type the desired type
     * @return The same SExpr, but with the desired type
     * @throws SMTTranslationException if an impossible conversion is attempted
     */
    public static SExpr coerce(SExpr exp, Type type) throws SMTTranslationException {
        assert type != null;
        assert exp != null;

        Type orgType = exp.getType();

        if (type == orgType) {
            // already of right type;
            return exp;
        }

        if (type == Type.UNIVERSE) {
            // Use the injection to go to universe
            if (orgType.injection == null) {
                throw new SMTTranslationException(
                    "Cannot inject from " + orgType + " into U: " + exp);
            }
            return new SExpr(orgType.injection, type, exp);
        }

        if (orgType == Type.UNIVERSE) {
            // Use the projection to go to other type
            if (type.projection == null) {
                throw new SMTTranslationException("Cannot project from U to " + type + ": " + exp);
            }
            return new SExpr(type.projection, type, exp);
        }

        throw new SMTTranslationException(
            "Cannot coerce from " + orgType + " to " + type + ": " + exp);
    }

    /**
     * Takes a list of {@link SExpr}s and converts it to a list of the given type, if possible.
     *
     * @param exprs the list to convert
     * @param type the desired target type
     * @return A fresh list with the same SExpr, but with the desired type
     * @throws SMTTranslationException if an impossible conversion is attempted
     */
    public static List<SExpr> coerce(List<SExpr> exprs, Type type) throws SMTTranslationException {
        List<SExpr> result = new ArrayList<>();
        for (SExpr expr : exprs) {
            result.add(coerce(expr, type));
        }
        return result;
    }

    /**
     * Produce a smt matching pattern. The result is {@code (! e :patterns ((patterns))}.
     *
     * If the list is empty, then {@code e} is returned.
     *
     * @param e the expression to wrap
     * @param patterns a possibly empty list of expressions
     * @return the expanded pattern with the same type as e
     */
    public static SExpr patternSExpr(SExpr e, SExpr... patterns) {
        return patternSExpr(e, Arrays.asList(patterns));
    }

    /**
     * Wrap the provided expression with a name label.
     * Result is {@code (e :named name)}.
     *
     * @param e expression
     * @param name label
     * @return the named expr
     */
    public static SExpr named(SExpr e, String name) {
        ArrayList<SExpr> children = new ArrayList<>();
        children.add(e);
        children.add(new SExpr(":named", Type.VERBATIM));
        children.add(new SExpr(name));
        return new SExpr("!", e.getType(), children);
    }

    /**
     * Produce a smt matching pattern. The result is {@code (! e :patterns ((patterns))}.
     *
     * If the list is empty, then {@code e} is returned.
     *
     * @param e the expression to wrap
     * @param patterns a possibly empty collection of expressions
     * @return the expanded pattern with the same type as e
     */
    public static SExpr patternSExpr(SExpr e, List<SExpr> patterns) {
        if (patterns.isEmpty()) {
            return e;
        }

        ArrayList<SExpr> children = new ArrayList<>();
        children.add(e);
        children.add(new SExpr(":pattern", Type.VERBATIM));
        children.add(new SExpr(patterns));
        return new SExpr("!", e.getType(), children);
    }

    /**
     * Turn a KeY sort into an SMT sort (by prefixing {@link #SORT_PREFIX}.
     *
     * @param sort the sort to translate to SMT
     * @return an SEXpr representing the sort (of type T)
     */
    public static SExpr sortExpr(Sort sort) {
        return new SExpr(SORT_PREFIX + sort.toString());
    }

    /**
     * Produce a cast expression
     *
     * @param sortExp the sort as an SExpr
     * @param exp the expression to cast
     * @return a cast of type exp to sort sortExp
     * @throws SMTTranslationException if coercion fails
     */
    public static SExpr castExpr(SExpr sortExp, SExpr exp) throws SMTTranslationException {
        // There is a coercion to Universe before the call.
        // What if a "Int" is given, it would fai otherwise.
        return new SExpr("cast", Type.UNIVERSE, coerce(exp, Type.UNIVERSE), sortExp);
    }

    /**
     * Produce an anssertion. The argument will be coerced to Bool.
     *
     * @param assertion the SExpr to wrap.
     * @return a freshly created assert SExpr.
     * @throws SMTTranslationException if coercion fails
     */
    public static SExpr assertion(SExpr assertion) throws SMTTranslationException {
        return new SExpr("assert", coerce(assertion, Type.BOOL));
    }

    /**
     * Collects the :pattern annations from any nesting depth in a term and brings it to toplevel.
     *
     * Example:
     *
     * <pre>
     *     (and (! (.A.) :pattern ((p1))) (! (.B.) :pattern ((p2))) )
     * </pre>
     *
     * yields
     *
     * <pre>
     *     (! (and (.A.) (.B:)) :pattern ((p1)(p2)))
     * </pre>
     *
     * @param matrix the SExpr to pull the patterns from
     * @return either matrix (if no patterns present) or a term (!... :pattern ...)
     */
    public static SExpr pullOutPatterns(SExpr matrix) {
        Set<SExpr> collected = new HashSet<>();
        matrix = filterAndCollectPatterns(matrix, collected);
        if (collected.isEmpty()) {
            return matrix;
        } else {
            return patternSExpr(matrix, collected.toArray(new SExpr[0]));
        }
    }

    private static SExpr filterAndCollectPatterns(SExpr matrix, Set<SExpr> collected) {
        List<SExpr> orgChildren = matrix.getChildren();
        if (matrix.getName().equals("!")) {
            collected.addAll(orgChildren.get(2).getChildren());
            return filterAndCollectPatterns(orgChildren.get(0), collected);
        }
        List<SExpr> children = null;
        for (int i = 0; i < orgChildren.size(); i++) {
            SExpr repl = filterAndCollectPatterns(orgChildren.get(i), collected);
            if (repl != orgChildren.get(i)) {
                if (children == null) {
                    children = new ArrayList<>(orgChildren);
                }
                children.set(i, repl);
            }
        }
        if (children == null) {
            return matrix;
        }
        return new SExpr(matrix.getName(), matrix.getType(), children);
    }

    // The following are simple application methods and should be self-explaining.

    public static SExpr instanceOf(SExpr var, SExpr sortExpr) {
        return new SExpr("instanceof", Type.BOOL, var, sortExpr);
    }

    public static SExpr greaterEqual(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr(">=", Type.BOOL, SExprs.coerce(a, IntegerOpHandler.INT),
            SExprs.coerce(b, IntegerOpHandler.INT));
    }

    public static SExpr lessEqual(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr("<=", Type.BOOL, SExprs.coerce(a, IntegerOpHandler.INT),
            SExprs.coerce(b, IntegerOpHandler.INT));
    }

    public static SExpr lessThan(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr("<", Type.BOOL, SExprs.coerce(a, IntegerOpHandler.INT),
            SExprs.coerce(b, IntegerOpHandler.INT));
    }

    public static SExpr eq(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr("=", Type.BOOL, a, b);
    }

    public static SExpr minus(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr("-", IntegerOpHandler.INT, SExprs.coerce(a, IntegerOpHandler.INT),
            SExprs.coerce(b, IntegerOpHandler.INT));
    }

    public static SExpr plus(SExpr a, SExpr b) throws SMTTranslationException {
        return new SExpr("+", IntegerOpHandler.INT, SExprs.coerce(a, IntegerOpHandler.INT),
            SExprs.coerce(b, IntegerOpHandler.INT));
    }

    public static SExpr ite(SExpr cond, SExpr _then, SExpr _else) throws SMTTranslationException {
        return new SExpr("ite", Type.UNIVERSE, SExprs.coerce(cond, Type.BOOL),
            SExprs.coerce(_then, Type.UNIVERSE), SExprs.coerce(_else, Type.UNIVERSE));
    }

    public static SExpr let(String var, SExpr val, SExpr in) {
        return new SExpr("let", new SExpr(new SExpr(var, val)), in);
    }

}
