package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class CastHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to do here
    }

    @Override
    public boolean canHandle(Term term) {
        return term.op().toString().contains("cast"); //TODO igitt
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        return new SExpr("cast", Type.UNIVERSE, inner, SExpr.sortExpr(op.getSortDependingOn()));
    }

}
