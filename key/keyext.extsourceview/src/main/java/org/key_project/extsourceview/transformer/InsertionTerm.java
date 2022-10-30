package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;

import java.io.IOException;

public class InsertionTerm {
    public final InsertionType Type;
    public final de.uka.ilkd.key.logic.Term Term;

    public InsertionTerm(InsertionType type, de.uka.ilkd.key.logic.Term term) {
        Type = type;
        Term = term;
    }

    public String toJMLString(Services svc) throws IOException {
        return SequentBackTransformer.TermToString(Term, svc); //TODO convert-term-to-jml method
    }
}
