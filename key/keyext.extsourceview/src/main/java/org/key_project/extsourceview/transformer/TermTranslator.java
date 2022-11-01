package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
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
        return or.sourceString().orElse("");
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

    public String translate(InsertionTerm iterm) throws TransformException {
        if (iterm.Type == InsertionType.ENSURES) {
            return "// @assume " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.REQUIRES) {
            return "// @assert " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.ASSIGNABLE) {
            return "// @assignable (TODO);";
        } else {
            throw  new TransformException("Unknown value for InsertionType");
        }
    }

    public String translateSafe(Term term) {
        try {
            return translate(term);
        } catch (TransformException e) {
            return "";
        }
    }

    public String translate(Term term) throws TransformException {
        OriginRef origin = term.getOriginRef();

        // simple case - use origin directly

        if (origin != null && origin.TermCoreHash == term.hashCodeCore()) {
            if (origin.hasFile()) {
                var r = origin.sourceString();
                if (r.isEmpty()) {
                    throw new TransformException("Failed to get origin of term");
                }
                return r.get();
            } else {
                throw new TransformException("TermOrigin is not from input");
            }
        }

        if (term.op() == Junctor.OR) return String.format("(%s) || (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.AND) return String.format("(%s) && (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.IMP) return String.format("(%s) -> (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.NOT) return String.format("!(%s)", translate(term.sub(0)));
        if (term.op() == Junctor.TRUE) return "true";
        if (term.op() == Junctor.FALSE) return "false";
        if (term.op() == Equality.EQUALS) return String.format("(%s) == (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Equality.EQV) return String.format("(%s) <-> (%s)", translate(term.sub(0)), translate(term.sub(1)));

        throw new TransformException("Failed to translate term (unsupported op)");
    }
}
