package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

/**
 * @author Rosa Abbasi, Jonas Schiffl, Mattias Ulbrich
 */
public class FloatHandler implements SMTHandler {

    public static final Type FLOAT = new Type("Float", "f2u", "u2f");
    public static final Type DOUBLE = new Type("Double", "d2u", "u2d");

    /** Java's FP semantics is always "round to nearest even". */
    private static final String ROUNDING_MODE = "RNE";

    public static final BooleanProperty DISABLE_SQRT_AXIOMS_PROPERTY =
            new BooleanProperty("disableSqrtAxiomatization",
                    "Disable axiomatization for sqrt",
                    "Disable quantified axioms for floating point sqrt which can increase runtime by a lot.");

    private final Map<Operator, String> fpOperators = new HashMap<>();
    private final Set<String> roundingOperators = new HashSet<>();

    private FloatLDT floatLDT;
    private DoubleLDT doubleLDT;
    private Services services;

    private boolean disableSqrtAxiomatizing;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException {

        this.services = services;
        floatLDT = services.getTypeConverter().getFloatLDT();
        doubleLDT = services.getTypeConverter().getDoubleLDT();
        disableSqrtAxiomatizing = DISABLE_SQRT_AXIOMS_PROPERTY.get(services);

        // operators with arguments
        fpOperators.put(floatLDT.getLessThan(), "fp.lt");
        fpOperators.put(floatLDT.getGreaterThan(), "fp.gt");
        fpOperators.put(floatLDT.getLessOrEquals(), "fp.leq");
        fpOperators.put(floatLDT.getGreaterOrEquals(), "fp.geq");
//        fpOperators.put(floatLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        fpOperators.put(floatLDT.getAdd(), "fp.add");
        fpOperators.put(floatLDT.getSub(), "fp.sub");
        fpOperators.put(floatLDT.getMul(), "fp.mul");
        fpOperators.put(floatLDT.getDiv(), "fp.div");

// From the smtlib manual on floats:
//        (fp.isNormal (_ FloatingPoint eb sb) Bool)
//        (fp.isSubnormal (_ FloatingPoint eb sb) Bool)
//        (fp.isZero (_ FloatingPoint eb sb) Bool)
//        (fp.isInfinite (_ FloatingPoint eb sb) Bool)
//        (fp.isNaN (_ FloatingPoint eb sb) Bool)
//        (fp.isNegative (_ FloatingPoint eb sb) Bool)
//        (fp.isPositive (_ FloatingPoint eb sb) Bool)

        fpOperators.put(floatLDT.getIsPositive(), "fp.isPositive");
        fpOperators.put(floatLDT.getAbs(), "fp.abs");
        fpOperators.put(floatLDT.getIsNaN(), "fp.isNaN");
        fpOperators.put(floatLDT.getIsZero(), "fp.isZero");
        fpOperators.put(floatLDT.getIsNormal(), "fp.isNormal");
        fpOperators.put(floatLDT.getIsSubnormal(), "fp.isSubnormal");
        fpOperators.put(floatLDT.getIsInfinite(), "fp.isInfinite");
        fpOperators.put(floatLDT.getIsNegative(), "fp.isNegative");
        fpOperators.put(floatLDT.getIsPositive(), "fp.isPositive");
        fpOperators.put(floatLDT.getEquals(), "fp.eq");

//        // Double predicates and operations, translated identically to float operations
        fpOperators.put(doubleLDT.getLessThan(), "fp.lt");
        fpOperators.put(doubleLDT.getGreaterThan(), "fp.gt");
        fpOperators.put(doubleLDT.getLessOrEquals(), "fp.leq");
        fpOperators.put(doubleLDT.getGreaterOrEquals(), "fp.geq");
//        fpOperators.put(doubleLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        fpOperators.put(doubleLDT.getAdd(), "fp.add");
        fpOperators.put(doubleLDT.getSub(), "fp.sub");
        fpOperators.put(doubleLDT.getMul(), "fp.mul");
        fpOperators.put(doubleLDT.getDiv(), "fp.div");

        fpOperators.put(doubleLDT.getIsPositive(), "fp.isPositive");
        fpOperators.put(doubleLDT.getAbs(), "fp.abs");
        fpOperators.put(doubleLDT.getIsNaN(), "fp.isNaN");
        fpOperators.put(doubleLDT.getIsZero(), "fp.isZero");
        fpOperators.put(doubleLDT.getIsNormal(), "fp.isNormal");
        fpOperators.put(doubleLDT.getIsSubnormal(), "fp.isSubnormal");
        fpOperators.put(doubleLDT.getIsInfinite(), "fp.isInfinite");
        fpOperators.put(doubleLDT.getIsNegative(), "fp.isNegative");
        fpOperators.put(doubleLDT.getIsPositive(), "fp.isPositive");
        fpOperators.put(doubleLDT.getEquals(), "fp.eq");

        if(disableSqrtAxiomatizing) {
            // Our own functions which are not built in.
            fpOperators.put(doubleLDT.getSqrtDouble(), "sqrtDouble");
            // fpOperators.put(floatLDT.getSqrtFloat(), "sqrtFloat");
        } else {
            // Use the builtin sqrt functions:
            fpOperators.put(doubleLDT.getSqrtDouble(), "fp.sqrt");
            // fpOperators.put(floatLDT.getSqrtFloat(), "fp.sqrt");
        }
//
//        mathOperators.put(doubleLDT.getSinDouble(), SMTTermFloatOp.Op.SINDOUBLE);
//        mathOperators.put(doubleLDT.getCosDouble(), SMTTermFloatOp.Op.COSDOUBLE);
//        mathOperators.put(doubleLDT.getAcosDouble(), SMTTermFloatOp.Op.ACOSDOUBLE);
//        mathOperators.put(doubleLDT.getAsinDouble(), SMTTermFloatOp.Op.ASINDOUBLE);
//        mathOperators.put(doubleLDT.getTanDouble(), SMTTermFloatOp.Op.TANDOUBLE);
//        mathOperators.put(doubleLDT.getAtan2Double(), SMTTermFloatOp.Op.ATAN2DOUBLE);
//        mathOperators.put(doubleLDT.getSqrtDouble(), SMTTermFloatOp.Op.SQRTDOUBLE);
//        mathOperators.put(doubleLDT.getPowDouble(), SMTTermFloatOp.Op.POWDOUBLE);
//        mathOperators.put(doubleLDT.getExpDouble(), SMTTermFloatOp.Op.EXPDOUBLE);
//        mathOperators.put(doubleLDT.getAtanDouble(), SMTTermFloatOp.Op.ATANDOUBLE);

        // These operators take a round mode argument:
        roundingOperators.addAll(Arrays.asList("fp.add", "fp.mul", "fp.sub", "fp.div", "fp.sqrt"));

        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {
        return fpOperators.containsKey(op)
                || op == floatLDT.getFloatSymbol()
                || op == doubleLDT.getDoubleSymbol();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        trans.introduceSymbol("float");
        trans.introduceSymbol("double");
        // sorts are defined here, declare them as already defined
        //trans.addSort(doubleLDT.targetSort());
        //trans.addSort(floatLDT.targetSort());

        Operator op = term.op();
        String fpOp = fpOperators.get(op);
        if(fpOp != null) {
            trans.introduceSymbol(fpOp);

            Sort sort = term.sort();
            Type exprType = getType(sort);

            ImmutableArray<Term> subs = term.subs();

            List<SExpr> translatedSubs = new LinkedList<>();

            if(roundingOperators.contains(fpOp)) {
                translatedSubs.add(new SExpr(ROUNDING_MODE));
            }

            for (Term t : subs) {
                Type type = getType(t.sort());
                translatedSubs.add(trans.translate(t, type));
            }

            return new SExpr(fpOp, exprType, translatedSubs);
        }

        if (op == doubleLDT.getDoubleSymbol()) {
            return doubleLiteralToSMT(term, services);
        } else if (op == floatLDT.getFloatSymbol()) {
            return floatLiteralToSMT(term, services);
        }

        throw new SMTTranslationException("Unhandled case: " + term);
    }

    private Type getType(Sort sort) throws SMTTranslationException {
        Type exprType;
        if (sort.equals(floatLDT.targetSort())) {
            exprType = FLOAT;
        } else if (sort.equals(doubleLDT.targetSort())) {
            exprType = DOUBLE;
        } else if (sort.equals(Sort.FORMULA)) {
            exprType = Type.BOOL;
        } else {
            throw new SMTTranslationException("Unexpected sort: " + sort);
        }
        return exprType;
    }

    /**
     * Translate a float literal of sort "float" in FP notation to
     * an SMTLIB fp literal
     *
     * @param term an application of FP
     * @return A string containing the translated literal
     */
    public static SExpr floatLiteralToSMT(Term term, Services services) {

        long repr = intFromTerm(term.sub(0), services);
        assert repr <= 0xffff_ffffL;

        String sign = "#b" + extractBits(repr, 31, 1);
        String exp = "#b" + extractBits(repr, 23, 8);
        String mantissa = "#b" + extractBits(repr, 0, 23);

        return new SExpr("fp", FloatHandler.FLOAT, sign, exp, mantissa);
    }

    /**
     * Translate a double literal of sort "double" in DFP notation to
     * an SMTLIB fp literal
     *
     * @param term an application of DFP
     * @return An sexpr containing the translated literal
     */
    public static SExpr doubleLiteralToSMT(Term term, Services services) {

        long repr = intFromTerm(term.sub(0), services);

        String sign = "#b" + extractBits(repr, 63, 1);
        String exp = "#b" + extractBits(repr, 52, 11);
        String mantissa = "#b" + extractBits(repr, 0, 52);

        return new SExpr("fp", FloatHandler.DOUBLE, sign, exp, mantissa);
    }

    private static String extractBits(long value, int fromBit, int count) {
        StringBuilder sb = new StringBuilder();
        value = value >>> fromBit;
        for (int i = 0; i < count; i++) {
            sb.insert(0, (value & 1) == 1 ? "1" : "0");
            value >>>= 1;
        }
        return sb.toString();
    }

    private static long intFromTerm(Term term, Services services) {
        if(term.op() == services.getTypeConverter().getIntegerLDT().getNumberTerminator()) {
            return 0L;
        } else {
            int digit = Integer.parseInt(term.op().name().toString());
            return 10 * intFromTerm(term.sub(0), services) + digit;
        }
    }
}
