package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.Properties;

/**
 * This simple SMT translation handler takes care of logical variables.
 *
 * It merely adds "var_" in front of the variable name.
 *
 * @author Jonas Schiffl
 */
public class LogicalVariableHandler implements SMTHandler {

    static final String VAR_PREFIX = "var_";

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Operator op) {
        return op instanceof LogicVariable;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        return new SExpr(VAR_PREFIX + term, Type.UNIVERSE);
    }

}
