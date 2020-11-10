package de.uka.ilkd.key.smt.newsmt2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class IntegerOpHandler implements SMTHandler {

    private final Map<Operator, String> supportedOperators = new HashMap<>();
    private final Set<Operator> predicateOperators = new HashSet<>();
    private Function jDivision;

    @Override
    public void init(MasterHandler masterHandler, Services services) {
        supportedOperators.clear();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getAdd(), "+");
        supportedOperators.put(integerLDT.getMul(), "*");
        supportedOperators.put(integerLDT.getSub(), "-");
        supportedOperators.put(integerLDT.getDiv(), "div");
        supportedOperators.put(integerLDT.getNeg(), "-");
        jDivision = integerLDT.getJDivision();
        supportedOperators.put(jDivision, "jdiv");

        supportedOperators.put(integerLDT.getLessOrEquals(), "<=");
        predicateOperators.add(integerLDT.getLessOrEquals());
        supportedOperators.put(integerLDT.getLessThan(), "<");
        predicateOperators.add(integerLDT.getLessThan());
        supportedOperators.put(integerLDT.getGreaterOrEquals(), ">=");
        predicateOperators.add(integerLDT.getGreaterOrEquals());
        supportedOperators.put(integerLDT.getGreaterThan(), ">");
        predicateOperators.add(integerLDT.getGreaterThan());
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return supportedOperators.containsKey(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        List<SExpr> children = trans.translate(term.subs(), Type.INT);
        Operator op = term.op();
        String smtOp = supportedOperators.get(op);
        assert smtOp != null;

        if(op == jDivision) {
            trans.addFromSnippets("jdiv");
        }

        Type resultType;
        if(predicateOperators.contains(op)) {
            resultType = Type.BOOL;
        } else {
            resultType = Type.INT;
        }

        return new SExpr(smtOp, resultType, children);
    }

}
