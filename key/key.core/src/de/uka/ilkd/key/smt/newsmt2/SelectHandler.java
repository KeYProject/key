package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class SelectHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to do here
    }

    @Override
    public boolean canHandle(Term term) {
        return term.op().toString().contains("select"); // TODO igittigitt
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortedOperator op = (SortedOperator) term.op();
        return new SExpr("select", Type.UNIVERSE, term.sub(0).toString(), term.sub(1).toString(), term.sub(2).toString());
    }

}
