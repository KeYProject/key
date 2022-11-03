package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
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

        if (singleLine)
            v = v.replaceAll("\\r", "").replaceAll("\\n", " ");

        return v;
    }

    private static Term removeLabelRecursive(TermFactory tf, Term term) {
        // Update children
        List<Term> newSubs = new LinkedList<>();
        for (Term oldSub : term.subs()) {
            newSubs.add(removeLabelRecursive(tf, oldSub));
        }

        return tf.createTerm(term.op(), new ImmutableArray<>(newSubs), term.boundVars(),
            term.javaBlock(), null, term.getOriginRef());
    }

    public String translate(InsertionTerm iterm) throws TransformException {
        if (iterm.Type == InsertionType.ASSUME) {
            return "// @assume " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return "// @assume (ERROR);";
        } else if (iterm.Type == InsertionType.ASSERT) {
            return "// @assert " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return "// @assert (ERROR);";
        } else if (iterm.Type == InsertionType.ASSIGNABLE) {
            return "// @assignable (TODO);"; // TODO assignables
        } else {
            throw new TransformException("Unknown value for InsertionType");
        }
    }

    public String translateSafe(InsertionTerm iterm) {
        try {
            return translate(iterm);
        } catch (TransformException e) {
            return "// @unknown (TRANSLATE-ERROR);";
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

        if (origin != null && unmodifiedTerm(origin.SourceTerm, term) && origin.hasFile()) {
            var r = origin.sourceString();
            if (r.isEmpty()) {
                throw new TransformException("Failed to get origin of term");
            }
            return r.get();
        }

        // handle annoying special cases

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP
                && term.op().name().toString().equals("wellFormed") && term.arity() == 1
                && term.sub(0).op().name().toString().equals("heap")) {
            return "\\wellFormed(heap)"; // TODO not valid JML
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED
                && term.op() == Equality.EQUALS && term.sub(1).op().name().toString().equals("TRUE")
                && term.sub(0).op().name().toString().equals("boolean::select")
                && term.sub(0).arity() == 3
                && term.sub(0).sub(0).op().name().toString().equals("heap")
                && term.sub(0).sub(1).op().name().toString().equals("self") && term.sub(0).sub(2)
                        .op().name().toString().equals("java.lang.Object::<created>")) {
            return "\\created(heap)"; // TODO not valid JML
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE
                && term.op() == Equality.EQUALS && term.sub(1).op().name().toString().equals("TRUE")
                && term.sub(0).op().name().toString().endsWith("::exactInstance")
                && term.sub(0).arity() == 1
                && term.sub(0).sub(0).op().name().toString().equals("self")) {
            return "\\exactInstance(self)"; // TODO not valid JML
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL
                && term.op().name().toString().equals("measuredByEmpty")) {
            return "\\measuredByEmpty()"; // TODO not valid JML
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL
                && term.op() == Equality.EQUALS && term.sub(0).op().name().toString().equals("self")
                && term.sub(1).op().name().toString().equals("null")) {
            return "this == null";
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_ENSURES_SELFINVARIANT
                && term.op().name().toString().equals("java.lang.Object::<inv>")
                && term.sub(1).op().name().toString().equals("self")) {
            return "\\invariant_for(this)"; // TODO hacky
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT
                && term.op().name().toString().equals("java.lang.Object::<inv>")
                && term.sub(1).op().name().toString().equals("self")) {
            return "\\invariant_for(this)"; // TODO hacky
        }

        // try to manually build the JML

        if (term.op() == Junctor.OR)
            return String.format("(%s) || (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.AND)
            return String.format("(%s) && (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.IMP)
            return String.format("(%s) -> (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Junctor.NOT)
            return String.format("!(%s)", translate(term.sub(0)));
        if (term.op() == Junctor.TRUE)
            return "true";
        if (term.op() == Junctor.FALSE)
            return "false";
        if (term.op() == Equality.EQUALS)
            return String.format("(%s) == (%s)", translate(term.sub(0)), translate(term.sub(1)));
        if (term.op() == Equality.EQV)
            return String.format("(%s) <-> (%s)", translate(term.sub(0)), translate(term.sub(1)));

        // all hope is lost - error out

        if (origin != null) {
            unmodifiedTerm(origin.SourceTerm, term);
        }

        throw new TransformException(
            "Failed to translate term (unsupported op): " + translateRaw(term, true));
    }

    private static boolean unmodifiedTerm(Term a, Term b) {
        if (a == b)
            return true;

        // TODO improve me

        // remove heap expressions
        while (a.op() instanceof Function && a.op().name().toString().equals("store")
                && a.arity() == 4 && a.sub(0).op().name().toString().equals("heap")
                && a.sub(1).op().name().toString().equals("self")) {
            a = a.sub(0);
        }
        while (b.op() instanceof Function && b.op().name().toString().equals("store")
                && b.arity() == 4 && b.sub(0).op().name().toString().equals("heap")
                && b.sub(1).op().name().toString().equals("self")) {
            b = b.sub(0);
        }

        // remove updates
        while (a.op() instanceof UpdateSV) {
            a = a.sub(0);
        }
        while (b.op() instanceof UpdateSV) {
            b = b.sub(0);
        }

        if (a.op().hashCode() != b.op().hashCode())
            return false;

        if (a.arity() != b.arity())
            return false;

        if (a.javaBlock() != b.javaBlock())
            return false;

        if (a.boundVars() != b.boundVars())
            return false;

        for (int i = 0; i < a.arity(); i++) {

            if (!unmodifiedTerm(a.sub(i), b.sub(i)))
                return false;

        }

        return true;
    }
}
