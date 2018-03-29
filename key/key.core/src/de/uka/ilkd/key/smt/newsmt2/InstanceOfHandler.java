package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.ExactInstanceof;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class InstanceOfHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to do here
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op.toString().contains("instance") || op.toString().contains("exactInstance");
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        if (op.toString().contains("exactInstance")) { // TODO das muss besser
                                                       // gehen
            SExpr res = new SExpr("=", Type.BOOL,
                    new SExpr("typeof", Type.BOOL, inner),
                    SExpr.sortExpr(op.getSortDependingOn()));
            return res;
        } else if (op.toString().contains("instance")) { // TODO das auch
            SExpr res = new SExpr("subtype", Type.BOOL,
                    new SExpr("typeof", Type.BOOL, inner),
                    SExpr.sortExpr(op.getSortDependingOn()));
            return res;
        } else {
            return null;
        }
    }
}
