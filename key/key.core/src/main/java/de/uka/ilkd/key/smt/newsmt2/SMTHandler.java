package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.net.URL;

public interface SMTHandler {

    void init(Services services) throws IOException;

    boolean canHandle(Term term);

    SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException;

    default URL getSnippetResource() {
        String resourceName = getClass().getSimpleName() + ".preamble.xml";
        return getClass().getResource(resourceName);
    }
}
