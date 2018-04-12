package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SMTTranslationException;

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
        // TODO Auto-generated method stub
        return null;
    }

}
