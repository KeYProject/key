package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class TermTranslator {

    private final Services svc;

    public TermTranslator(Services services) {
        svc = services;
    }

    public String translateWithOrigin(Term term) {
        OriginRef or = term.getOriginRef();
        if (or == null) {
            return "";
        }
        return or.sourceString();
    }

    public String translateRaw(Term term, boolean singleLine) {
        var ni = new NotationInfo();

        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(), ni, svc);
        ni.refresh(svc, true, false);

        term = removeLabelRecursive(svc.getTermFactory(), term);

        try {
            printer.printTerm(term);
        } catch (IOException e) {
            return "[ERROR]";
        }

        var v = printer.toString();

        if (singleLine) v = v.replaceAll("\\r", "").replaceAll("\\n", " ");

        return v;
    }

    private static Term removeLabelRecursive(TermFactory tf, Term term) {
        // Update children
        List<Term> newSubs = new LinkedList<>();
        for (Term oldSub : term.subs()) {
            newSubs.add(removeLabelRecursive(tf, oldSub));
        }

        return tf.createTerm(term.op(), new ImmutableArray<>(newSubs), term.boundVars(), term.javaBlock(), null, term.getOriginRef());
    }
}
