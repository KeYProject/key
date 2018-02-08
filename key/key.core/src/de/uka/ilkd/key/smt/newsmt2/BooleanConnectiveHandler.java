package de.uka.ilkd.key.smt.newsmt2;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class BooleanConnectiveHandler implements SMTHandler {

    private final Map<Operator, String> supportedOperators = new HashMap<>();
    {
        supportedOperators.put(Junctor.AND, "and");
        supportedOperators.put(Junctor.OR, "or");
        supportedOperators.put(Junctor.IMP, "=>");
        supportedOperators.put(Junctor.NOT, "not");
        supportedOperators.put(Junctor.FALSE, "false");
        supportedOperators.put(Junctor.TRUE, "true");
        supportedOperators.put(Equality.EQV, "=");
    };

    private Operator logicFalse;
    private Operator logicTrue;

    @Override
    public void init(Services services) {
        BooleanLDT ldt = services.getTypeConverter().getBooleanLDT();

        if(logicFalse != null) {
            supportedOperators.remove(logicFalse);
        }
        this.logicFalse = ldt.getFalseConst();
        supportedOperators.put(logicFalse, "false");

        if(logicTrue != null) {
            supportedOperators.remove(logicTrue);
        }
        this.logicTrue = ldt.getTrueConst();
        supportedOperators.put(logicFalse, "true");
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return supportedOperators.containsKey(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        List<SExpr> children = trans.translate(term.subs(), Type.BOOL);
        Operator op = term.op();
        String smtOp = supportedOperators.get(op);
        assert smtOp != null;
        return new SExpr(smtOp, Type.BOOL, children);
    }

}
