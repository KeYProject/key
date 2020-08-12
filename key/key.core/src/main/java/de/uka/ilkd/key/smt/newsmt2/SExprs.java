package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;

public class SExprs {

    public static final SExpr TRUE = new SExpr("true", Type.BOOL);
    public static final SExpr FALSE = new SExpr("false", Type.BOOL);

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

    public static SExpr imp(SExpr ante, SExpr cons) {
        if(ante.equals(TRUE)) {
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

    private static SExpr not(SExpr se) {
        return new SExpr("not", Type.BOOL, se);
    }

    public static SExpr forall(List<SExpr> vars, SExpr matrix) {
        if (vars.isEmpty()) {
            if (matrix.getName().equals("!")) {
                return matrix.getChildren().get(0);
            }
            return matrix;
        } else {
            return new SExpr("forall", Type.BOOL, new SExpr(vars), matrix);
        }
    }

    /**
     * Takes an SExpression and converts it to the given type, if possible.
     * @param exp the SExpression to convert
     * @param type the desired type
     * @return The same SExpr, but with the desired type
     * @throws SMTTranslationException if an impossible conversion is attempted
     */
    public static SExpr coerce(SExpr exp, Type type) throws SMTTranslationException {
        switch(type) {
            case BOOL:
                switch(exp.getType()) {
                    case BOOL:
                        return exp;
                    case UNIVERSE:
                        return new SExpr("u2b", Type.BOOL, exp);
                    default:
                        throw new SMTTranslationException("Cannot convert to bool: " + exp);
                }
            case INT:
                switch(exp.getType()) {
                    case INT:
                        return exp;
                    case UNIVERSE:
                        return new SExpr("u2i", Type.INT, exp);
                    default:
                        throw new SMTTranslationException("Cannot convert to int: " + exp);
                }
            case UNIVERSE:
                switch(exp.getType()) {
                    case UNIVERSE:
                        return exp;
                    case INT:
                        return new SExpr("i2u", Type.UNIVERSE, exp);
                    case BOOL:
                        return new SExpr("b2u", Type.UNIVERSE, exp);
                    default:
                        throw new SMTTranslationException("Cannot convert to universe: " + exp);
                }
            default:
                throw new SMTTranslationException("Cannot convert into " + type);
        }
    }

    public static List<SExpr> coerce(List<SExpr> exprs, Type type) throws SMTTranslationException {
        List<SExpr> result = new ArrayList<>();
        for (SExpr expr : exprs) {
            result.add(coerce(expr, type));
        }
        return result;
    }

    static SExpr patternSExpr(SExpr e, SExpr... patterns) {
        ArrayList<SExpr> children = new ArrayList<>();
        children.add(e);
        children.add(new SExpr(":pattern", Type.VERBATIM));
        children.addAll(Arrays.asList(patterns));
        return new SExpr("!", e.getType(), children);
    }

    static SExpr sortExpr(Sort sort) {
        return new SExpr(ModularSMTLib2Translator.SORT_PREFIX + sort.toString());
    }

    static SExpr castExpr(SExpr sortExp, SExpr exp) {
        // REVIEW MU: Should there perhaps be a coercion to Universe before the call?
        // What if a "Int" is given. That would fail.
        return new SExpr("cast", Type.UNIVERSE, exp, sortExp);
    }

}
