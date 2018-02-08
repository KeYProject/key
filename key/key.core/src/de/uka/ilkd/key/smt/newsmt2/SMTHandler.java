package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SMTTranslationException;

public interface SMTHandler {

    void init(Services services);

    boolean canHandle(Term term);

    SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException;
}
