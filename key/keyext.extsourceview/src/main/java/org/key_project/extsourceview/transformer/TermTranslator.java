package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.*;

public class TermTranslator {

    private final Services svc;

    public Map<String, String> nullaryFuncs = Map.ofEntries(
            new AbstractMap.SimpleEntry<>("null", "null"),
            new AbstractMap.SimpleEntry<>("TRUE", "true"),
            new AbstractMap.SimpleEntry<>("FALSE", "false"),
            new AbstractMap.SimpleEntry<>("self", "this")
    );

    public Map<String, String> bracketFuncs = Map.ofEntries(
            new AbstractMap.SimpleEntry<>("wellFormed", "\\wellFormed"),
            new AbstractMap.SimpleEntry<>("java.lang.Object::<inv>", "\\invariant_for")
    );

    public Map<String, String> inlineFuncs = Map.ofEntries(
            new AbstractMap.SimpleEntry<>("or", "%s || %s"),
            new AbstractMap.SimpleEntry<>("and", "%s && %s"),
            new AbstractMap.SimpleEntry<>("imp", "%s -> %s"),

            new AbstractMap.SimpleEntry<>("not", "!%s"),

            new AbstractMap.SimpleEntry<>("equals", "%s == %s"),
            new AbstractMap.SimpleEntry<>("equiv", "%s <-> %s"),

            new AbstractMap.SimpleEntry<>("add", "%s + %s"),
            new AbstractMap.SimpleEntry<>("neg", "-%s"),
            new AbstractMap.SimpleEntry<>("sub", "%s - %s"),
            new AbstractMap.SimpleEntry<>("mul", "%s * %s"),
            new AbstractMap.SimpleEntry<>("div", "%s / %s"),
            new AbstractMap.SimpleEntry<>("mod", "%s % %s"),
            //new AbstractMap.SimpleEntry<>("pow", ""),

            new AbstractMap.SimpleEntry<>("lt", "%s < %s"),
            new AbstractMap.SimpleEntry<>("gt", "%s > %s"),
            new AbstractMap.SimpleEntry<>("geq", "%s >= %s"),
            new AbstractMap.SimpleEntry<>("leq", "%s <= %s"),

            //new AbstractMap.SimpleEntry<>("bsum", ""),
            //new AbstractMap.SimpleEntry<>("bprod", ""),
            //new AbstractMap.SimpleEntry<>("jdiv", ""),
            //new AbstractMap.SimpleEntry<>("jmod", ""),
            //new AbstractMap.SimpleEntry<>("unaryMinusJint", ""),
            //new AbstractMap.SimpleEntry<>("unaryMinusJlong", ""),
            //new AbstractMap.SimpleEntry<>("addJint", ""),
            //new AbstractMap.SimpleEntry<>("addJlong", ""),
            //new AbstractMap.SimpleEntry<>("subJint", ""),
            //new AbstractMap.SimpleEntry<>("subJlong", ""),
            //new AbstractMap.SimpleEntry<>("mulJint", ""),
            //new AbstractMap.SimpleEntry<>("mulJlong", ""),
            //new AbstractMap.SimpleEntry<>("modJint", ""),
            //new AbstractMap.SimpleEntry<>("modJlong", ""),
            //new AbstractMap.SimpleEntry<>("divJint", ""),
            //new AbstractMap.SimpleEntry<>("divJlong", ""),

            new AbstractMap.SimpleEntry<>("shiftright", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("shiftleft", "%s << %s"),

            //new AbstractMap.SimpleEntry<>("shiftrightJint", ""),
            //new AbstractMap.SimpleEntry<>("shiftrightJlong", ""),
            //new AbstractMap.SimpleEntry<>("shiftleftJint", ""),
            //new AbstractMap.SimpleEntry<>("shiftleftJlong", ""),
            //new AbstractMap.SimpleEntry<>("unsignedshiftrightJint", ""),
            //new AbstractMap.SimpleEntry<>("unsignedshiftrightJlong", ""),

            new AbstractMap.SimpleEntry<>("binaryOr", "%s | %s"),
            new AbstractMap.SimpleEntry<>("binaryAnd", "%s & %s"),
            new AbstractMap.SimpleEntry<>("binaryXOr", "%s ^ %s")

            //new AbstractMap.SimpleEntry<>("orJint", ""),
            //new AbstractMap.SimpleEntry<>("orJlong", ""),
            //new AbstractMap.SimpleEntry<>("andJint", ""),
            //new AbstractMap.SimpleEntry<>("andJlong", ""),
            //new AbstractMap.SimpleEntry<>("xorJint", ""),
            //new AbstractMap.SimpleEntry<>("xorJlong", ""),

            //new AbstractMap.SimpleEntry<>("moduloByte", ""),
            //new AbstractMap.SimpleEntry<>("moduloShort", ""),
            //new AbstractMap.SimpleEntry<>("moduloInt", ""),
            //new AbstractMap.SimpleEntry<>("moduloLong", ""),
            //new AbstractMap.SimpleEntry<>("moduloChar", ""),

            //new AbstractMap.SimpleEntry<>("javaUnaryMinusInt", ""),
            //new AbstractMap.SimpleEntry<>("javaUnaryMinusLong", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseNegation", ""),
            //new AbstractMap.SimpleEntry<>("javaAddInt", ""),
            //new AbstractMap.SimpleEntry<>("javaAddLong", ""),
            //new AbstractMap.SimpleEntry<>("javaSubInt", ""),
            //new AbstractMap.SimpleEntry<>("javaSubLong", ""),
            //new AbstractMap.SimpleEntry<>("javaMulInt", ""),
            //new AbstractMap.SimpleEntry<>("javaMulLong", ""),
            //new AbstractMap.SimpleEntry<>("javaMod", ""),
            //new AbstractMap.SimpleEntry<>("javaDivInt", ""),
            //new AbstractMap.SimpleEntry<>("javaDivLong", ""),
            //new AbstractMap.SimpleEntry<>("javaShiftRightInt", ""),
            //new AbstractMap.SimpleEntry<>("javaShiftRightLong", ""),
            //new AbstractMap.SimpleEntry<>("javaShiftLeftInt", ""),
            //new AbstractMap.SimpleEntry<>("javaShiftLeftLong", ""),
            //new AbstractMap.SimpleEntry<>("javaUnsignedShiftRightInt", ""),
            //new AbstractMap.SimpleEntry<>("javaUnsignedShiftRightLong", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseOrInt", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseOrLong", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseAndInt", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseAndLong", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseXOrInt", ""),
            //new AbstractMap.SimpleEntry<>("javaBitwiseXOrLong", ""),
            //new AbstractMap.SimpleEntry<>("javaCastByte", ""),
            //new AbstractMap.SimpleEntry<>("javaCastShort", ""),
            //new AbstractMap.SimpleEntry<>("javaCastInt", ""),
            //new AbstractMap.SimpleEntry<>("javaCastLong", ""),
            //new AbstractMap.SimpleEntry<>("javaCastChar", ""),

            //new AbstractMap.SimpleEntry<>("inByte", ""),
            //new AbstractMap.SimpleEntry<>("inShort", ""),
            //new AbstractMap.SimpleEntry<>("inInt", ""),
            //new AbstractMap.SimpleEntry<>("inLong", ""),
            //new AbstractMap.SimpleEntry<>("inChar", ""),
            //new AbstractMap.SimpleEntry<>("index", "")
    );


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
            return "//@ assume " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return "//@ assume (ERROR);";
        } else if (iterm.Type == InsertionType.ASSERT) {
            return "//@ assert " + translate(iterm.Term) + ";";
        } else if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return "//@ assert (ERROR);";
        } else if (iterm.Type == InsertionType.ASSIGNABLE) {
            return "//@ assignable (TODO);"; // TODO assignables
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
            return "\\created(this)"; // TODO not valid JML
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE
                && term.op() == Equality.EQUALS && term.sub(1).op().name().toString().equals("TRUE")
                && term.sub(0).op().name().toString().endsWith("::exactInstance")
                && term.sub(0).arity() == 1
                && term.sub(0).sub(0).op().name().toString().equals("self")) {
            return "\\exactInstance(this)"; // TODO not valid JML
        }

        if (term.op().name().toString().endsWith("::exactInstance")
                && term.arity() == 1
                && term.sub(0).op().name().toString().equals("self")) {
            return "\\exactInstance(this)"; // TODO not valid JML
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
            return "\\invariant_for(this)";
        }

        if (origin != null && origin.Type == OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT
                && term.op().name().toString().equals("java.lang.Object::<inv>")
                && term.sub(1).op().name().toString().equals("self")) {
            return "\\invariant_for(this)";
        }

        if (term.op().name().toString().equals("not")
                && term.sub(0).op().name().toString().equals("equals")
                && term.sub(0).arity() == 2) {
            return String.format("%s != %s", bracketTranslate(term.sub(0), term.sub(0).sub(0)), bracketTranslate(term.sub(0), term.sub(0).sub(1)));
        }

        // try to manually build the JML

        if (term.op() instanceof LocationVariable && term.arity() == 0) {
            return term.op().name().toString();
        }

        if (term.op() instanceof Function && term.op().name().toString().equals("Z")) {
            return translateRaw(term, true);
        }

        if (term.op() instanceof Function && bracketFuncs.containsKey(term.op().name().toString())) {
            String keyword = bracketFuncs.get(term.op().name().toString());

            StringBuilder b = new StringBuilder();
            b.append(keyword);
            b.append("(");
            for (int i = 0; i < term.op().arity(); i++) {
                if (i > 0) b.append(", ");
                b.append(translate(term.sub(i)));
            }
            b.append(")");
            return b.toString();
        }

        if (term.op() instanceof Function && term.arity() == 0 && nullaryFuncs.containsKey(term.op().name().toString())) {
            return nullaryFuncs.get(term.op().name().toString());
        }

        if ((term.op() instanceof Function || term.op() instanceof AbstractSortedOperator) && inlineFuncs.containsKey(term.op().name().toString())) {
            String fmt = inlineFuncs.get(term.op().name().toString());

            Object[] p = new String[term.arity()];
            for (int i = 0; i < term.arity(); i++) {
                p[i] = bracketTranslate(term, term.sub(i));
            }
            return String.format(fmt, p);
        }

        if (term.op() instanceof Function && term.op().name().toString().equals("store")) {
            return translate(term.sub(2)); //TODO ??
        }

        // all hope is lost - error out

        if (origin != null) {
            unmodifiedTerm(origin.SourceTerm, term);
        }

        throw new TransformException("Failed to translate term (unsupported op): " + translateRaw(term, true));
    }

    private String bracketTranslate(Term base, Term child) throws TransformException {
        if (needsBrackets(base, child)) {
            return "(" + translate(child) + ")";
        } else {
            return translate(child);
        }
    }

    private boolean needsBrackets(Term base, Term child) {
        // this is by far not exhaustive, but more brackets are not an error

        if (child.op() instanceof LocationVariable) return false;
        if (child.op().arity() == 0) return false;
        if (child.op() instanceof Function && child.op().name().toString().equals("Z")) return false;
        if (child.op() instanceof Function && bracketFuncs.containsKey(child.op().name().toString())) return false;

        return true;
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
