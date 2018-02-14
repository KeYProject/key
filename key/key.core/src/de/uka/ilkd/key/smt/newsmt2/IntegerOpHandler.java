package de.uka.ilkd.key.smt.newsmt2;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class IntegerOpHandler implements SMTHandler {

    private Services services;
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(Services services) {
        this.services = services;
        supportedOperators.clear();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getAdd(), "+");
        supportedOperators.put(integerLDT.getMul(), "*");
        supportedOperators.put(integerLDT.getSub(), "-");
        supportedOperators.put(integerLDT.getDiv(), "/");
        supportedOperators.put(integerLDT.getNeg(), "-");

        supportedOperators.put(integerLDT.getLessOrEquals(), "<=");
        supportedOperators.put(integerLDT.getLessThan(), "<");
        supportedOperators.put(integerLDT.getGreaterOrEquals(), ">=");
        supportedOperators.put(integerLDT.getGreaterThan(), ">");
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

        Type resultType;
        if(smtOp.contains("<") || smtOp.contains(">")) {
            resultType = Type.BOOL;
        } else {
            resultType = Type.INT;
        }

        return new SExpr(smtOp, resultType, children);
    }

}
