package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class LogicalVariableHandler implements SMTHandler {

    static final String VAR_PREFIX = "var_";

    @Override
    public void init(Services services) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op instanceof LogicVariable;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        return new SExpr(VAR_PREFIX + term, Type.UNIVERSE);
    }

}
