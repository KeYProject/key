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
import java.net.URI;
import java.util.*;
import java.util.stream.Collectors;

/**
 * This class is used to translate a Term object (back) into a JML string
 * Such that it can be displayed in the SourceView.
 * The important function is translate(), which uses he term originRef's if possible
 */
public class TermTranslator {

    private final URI fileUri;
    private final Services svc;

    private final boolean enableFallbackTranslation;

    //TODO use better and more fail-safe way to handle this
    //     (see IntegerHandler.java)
    //     (see OverloadedOperatorHandler.java)
    //     (see HeapLDT.java)

    public Map<String, String> nullaryFuncs = Map.<String, String>ofEntries(
            new AbstractMap.SimpleEntry<>("null", "null"),
            new AbstractMap.SimpleEntry<>("TRUE", "true"),
            new AbstractMap.SimpleEntry<>("true", "true"),
            new AbstractMap.SimpleEntry<>("FALSE", "false"),
            new AbstractMap.SimpleEntry<>("false", "false"),
            new AbstractMap.SimpleEntry<>("self", "this")
    );

    public Map<String, String> bracketFuncs = Map.<String, String>ofEntries(
            new AbstractMap.SimpleEntry<>("wellFormed", "\\wellFormed"),
            new AbstractMap.SimpleEntry<>("java.lang.Object::<inv>", "\\invariant_for")
    );

    public Map<String, String> inlineFuncs = Map.<String, String>ofEntries(
            new AbstractMap.SimpleEntry<>("or", "%s || %s"),
            new AbstractMap.SimpleEntry<>("and", "%s && %s"),
            new AbstractMap.SimpleEntry<>("imp", "%s ==> %s"),

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

            new AbstractMap.SimpleEntry<>("unaryMinusJint", "-%s"),
            new AbstractMap.SimpleEntry<>("unaryMinusJlong", "-%s"),
            new AbstractMap.SimpleEntry<>("addJint", "%s + %s"),
            new AbstractMap.SimpleEntry<>("addJlong", "%s + %s"),
            new AbstractMap.SimpleEntry<>("subJint", "%s - %s"),
            new AbstractMap.SimpleEntry<>("subJlong", "%s - %s"),
            new AbstractMap.SimpleEntry<>("mulJint", "%s * %s"),
            new AbstractMap.SimpleEntry<>("mulJlong", "%s * %s"),
            new AbstractMap.SimpleEntry<>("modJint", "%s % %s"),
            new AbstractMap.SimpleEntry<>("modJlong", "%s % %s"),
            new AbstractMap.SimpleEntry<>("divJint", "%s / %s"),
            new AbstractMap.SimpleEntry<>("divJlong", "%s / %s"),

            new AbstractMap.SimpleEntry<>("shiftright", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("shiftleft", "%s << %s"),

            new AbstractMap.SimpleEntry<>("shiftrightJint", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("shiftrightJlong", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("shiftleftJint", "%s << %s"),
            new AbstractMap.SimpleEntry<>("shiftleftJlong", "%s << %s"),
            //new AbstractMap.SimpleEntry<>("unsignedshiftrightJint", ""),
            //new AbstractMap.SimpleEntry<>("unsignedshiftrightJlong", ""),

            new AbstractMap.SimpleEntry<>("binaryOr", "%s | %s"),
            new AbstractMap.SimpleEntry<>("binaryAnd", "%s & %s"),
            new AbstractMap.SimpleEntry<>("binaryXOr", "%s ^ %s"),

            new AbstractMap.SimpleEntry<>("orJint", "%s | %s"),
            new AbstractMap.SimpleEntry<>("orJlong", "%s | %s"),
            new AbstractMap.SimpleEntry<>("andJint", "%s & %s"),
            new AbstractMap.SimpleEntry<>("andJlong", "%s & %s"),
            new AbstractMap.SimpleEntry<>("xorJint", "%s ^ %s"),
            new AbstractMap.SimpleEntry<>("xorJlong", "%s ^ %s"),

            new AbstractMap.SimpleEntry<>("moduloByte", "%s % %s"),
            new AbstractMap.SimpleEntry<>("moduloShort", "%s % %s"),
            new AbstractMap.SimpleEntry<>("moduloInt", "%s % %s"),
            new AbstractMap.SimpleEntry<>("moduloLong", "%s % %s"),
            new AbstractMap.SimpleEntry<>("moduloChar", "%s % %s"),

            new AbstractMap.SimpleEntry<>("javaUnaryMinusInt", "-%s"),
            new AbstractMap.SimpleEntry<>("javaUnaryMinusLong", "-%s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseNegation", "~%s"),
            new AbstractMap.SimpleEntry<>("javaAddInt", "%s + %s"),
            new AbstractMap.SimpleEntry<>("javaAddLong", "%s + %s"),
            new AbstractMap.SimpleEntry<>("javaSubInt", "%s - %s"),
            new AbstractMap.SimpleEntry<>("javaSubLong", "%s - %s"),
            new AbstractMap.SimpleEntry<>("javaMulInt", "%s * %s"),
            new AbstractMap.SimpleEntry<>("javaMulLong", "%s * %s"),
            new AbstractMap.SimpleEntry<>("javaMod", "%s % %s"),
            new AbstractMap.SimpleEntry<>("javaDivInt", "%s / %s"),
            new AbstractMap.SimpleEntry<>("javaDivLong", "%s / %s"),
            new AbstractMap.SimpleEntry<>("javaShiftRightInt", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("javaShiftRightLong", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("javaShiftLeftInt", "%s << %s"),
            new AbstractMap.SimpleEntry<>("javaShiftLeftLong", "%s << %s"),
            new AbstractMap.SimpleEntry<>("javaUnsignedShiftRightInt", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("javaUnsignedShiftRightLong", "%s >> %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseOrInt", "%s | %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseOrLong", "%s | %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseAndInt", "%s & %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseAndLong", "%s & %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseXOrInt", "%s ^ %s"),
            new AbstractMap.SimpleEntry<>("javaBitwiseXOrLong", "%s ^ %s"),
            new AbstractMap.SimpleEntry<>("javaCastByte", "%s"),
            new AbstractMap.SimpleEntry<>("javaCastShort", "%s"),
            new AbstractMap.SimpleEntry<>("javaCastInt", "%s"),
            new AbstractMap.SimpleEntry<>("javaCastLong", "%s"),
            new AbstractMap.SimpleEntry<>("javaCastChar", "%s"),

            //new AbstractMap.SimpleEntry<>("inByte", ""),
            //new AbstractMap.SimpleEntry<>("inShort", ""),
            //new AbstractMap.SimpleEntry<>("inInt", ""),
            //new AbstractMap.SimpleEntry<>("inLong", ""),
            //new AbstractMap.SimpleEntry<>("inChar", ""),
            //new AbstractMap.SimpleEntry<>("index", ""),

            new AbstractMap.SimpleEntry<>("length", "%s.length"),
            //new AbstractMap.SimpleEntry<>("acc", ""),
            //new AbstractMap.SimpleEntry<>("reach", ""),
            new AbstractMap.SimpleEntry<>("prec", "%s < %s") //is this right?
    );


    public TermTranslator(URI fileUri, Services services, boolean enableFallback) {
        this.fileUri = fileUri;
        this.svc = services;
        this.enableFallbackTranslation = enableFallback;
    }

    public String translateWithOrigin(Term term) {
        ImmutableArray<OriginRef> or = term.getOriginRef();

        if (or.size() == 0) {
            return "";
        }
        return or.get(0).sourceString().orElse("");
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

        if (singleLine) {
            v = v.replaceAll("\\r", "").replaceAll("\\n", " ").replaceAll("[ ]{2,}", " ");
        }

        v = v.trim();

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

    public String translate(InsertionTerm iterm, InsPositionProvider pp, InsPositionProvider.InsertionPosition basePos) throws TransformException, InternTransformException {
        if (iterm.Type == InsertionType.ASSUME) {
            return "//@ assume " + translate(iterm.Term, pp, basePos.Line, iterm.Type) + ";";
        } else if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return "//@ assume (ERROR);";
        } else if (iterm.Type == InsertionType.ASSERT) {
            return "//@ assert " + translate(iterm.Term, pp, basePos.Line, iterm.Type) + ";";
        } else if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return "//@ assert (ERROR);";
        } else if (iterm.Type == InsertionType.ASSIGNABLE) {
            return "//@ assignable (TODO);"; // TODO assignables
        } else {
            throw new TransformException("Unknown value for InsertionType");
        }
    }

    public String translateSafe(InsertionTerm iterm, InsPositionProvider pp, InsPositionProvider.InsertionPosition basePos) {
        try {
            return translate(iterm, pp, basePos);
        } catch (TransformException | InternTransformException e) {
            return "//@ unknown (TRANSLATE-ERROR); //" + translateRaw(iterm.Term, true);
        }
    }

    public String translateSafe(Term term, InsertionType itype) {
        try {
            return translate(term, new DummyPositionProvider(), null, itype);
        } catch (TransformException | InternTransformException e) {
            return "";
        }
    }

    private String translate(Term term, InsPositionProvider pp, Integer termBasePos, InsertionType itype) throws TransformException, InternTransformException {
        var origin = term.getOriginRef()
                .stream()
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP)
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL)
                .filter(p -> p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());

        if (termBasePos != null) {
            var hp = pp.GetTermHeapPosition(term, itype);

            if (hp.isPresent()) {
                var hpnum = hp.get();
                if (hpnum == pp.getOldPos()+1) {
                    hpnum--;
                }

                if (!hpnum.equals(termBasePos)) {
                    if (pp.getOldPos().equals(hpnum)) {
                        return "\\old(" + translate(term, pp, hpnum, itype) + ")";
                    } else  {
                        return "\\old<"+hp.get()+">(" + translate(term, pp, hpnum, itype) + ")";
                    }
                }
            }

        }

        var heaps = MovingPositioner.listHeaps(term, true);

        if (origin.size() == 1 && (termBasePos == null || (heaps.size() == 1 && heaps.get(0).getLineNumber().orElse(-1).equals(termBasePos)) || (heaps.size() == 0))) {

            OriginRef singleorig = origin.get(0);

            // simple case - use origin directly

            if (singleorig.SourceTerm != null && origin.get(0).hasFile()) {
                var r = origin.get(0).sourceString();
                if (r.isEmpty()) {
                    throw new TransformException("Failed to get origin of term");
                }
                return r.get();
            }

            // handle annoying special cases

            if ((singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP
                    || singleorig.Type == OriginRefType.LOOP_INITIALLYVALID_WELLFORMED
                    || singleorig.Type == OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED
                    || singleorig.Type == OriginRefType.LOOP_USECASE_WELLFORMED)
                    && term.op().name().toString().equals("wellFormed") && term.arity() == 1
                    && term.sub(0).op().sort(term.sub(0).subs()).toString().equals("Heap")) {
                return "\\wellFormed("+term.sub(0).op().toString()+")"; // TODO not valid JML
            }

            if (singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED
                    && term.op() == Equality.EQUALS && term.sub(1).op().name().toString().equals("TRUE")
                    && term.sub(0).op().name().toString().equals("boolean::select")
                    && term.sub(0).arity() == 3
                    && term.sub(0).sub(0).op().name().toString().equals("heap")
                    && term.sub(0).sub(1).op().name().toString().equals("self") && term.sub(0).sub(2)
                    .op().name().toString().equals("java.lang.Object::<created>")) {
                return "\\created(this)"; // TODO not valid JML
            }

            if (singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE
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

            if (singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL
                    && term.op().name().toString().equals("measuredByEmpty")) {
                return "\\measuredByEmpty()"; // TODO not valid JML
            }

            if (singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL
                    && term.op() == Equality.EQUALS && term.sub(0).op().name().toString().equals("self")
                    && term.sub(1).op().name().toString().equals("null")) {
                return "this == null";
            }

            if (singleorig.Type == OriginRefType.IMPLICIT_ENSURES_SELFINVARIANT
                    && term.op().name().toString().equals("java.lang.Object::<inv>")
                    && term.sub(1).op().name().toString().equals("self")) {
                return "\\invariant_for(this)";
            }

            if (singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT
                    && term.op().name().toString().equals("java.lang.Object::<inv>")
                    && term.sub(1).op().name().toString().equals("self")) {
                return "\\invariant_for(this)";
            }

        }

        if (enableFallbackTranslation) {
            // ======= try to manually build the JML =======

            // special not-case

            if (term.op().name().toString().equals("not")
                    && term.sub(0).op().name().toString().equals("equals")
                    && term.sub(0).arity() == 2) {
                return String.format("%s != %s",
                        bracketTranslate(term.sub(0), term.sub(0).sub(0), pp, termBasePos, itype),
                        bracketTranslate(term.sub(0), term.sub(0).sub(1), pp, termBasePos, itype));
            }

            // Use OriginFuncNameMap

            if (term.op() instanceof Function && term.op().arity() == 0 && svc.getOriginFuncNameMap().has(term.op().name())) {
                return svc.getOriginFuncNameMap().get(term.op().name()).toString();
            }

            // ...

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
                    b.append(translate(term.sub(i), pp, termBasePos, itype));
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
                    p[i] = bracketTranslate(term, term.sub(i), pp, termBasePos, itype);
                }
                return String.format(fmt, p);
            }

            if (term.op() instanceof Function && term.op().name().toString().equals("store")) {
                return translate(term.sub(2), pp, termBasePos, itype); //TODO ??
            }

            if (term.op() == Quantifier.ALL && term.boundVars().size() == 1 && term.arity() == 1) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("\\forall %s %s; %s", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype));
            }

            if (term.op() == Quantifier.EX && term.boundVars().size() == 1 && term.arity() == 1) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("\\exists %s %s; %s", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype));
            }

            if (term.op() instanceof Function && term.op().name().toString().equals("created")) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("\\exists %s %s; %s", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype));
            }

            if (term.op().name().toString().equals("bsum") && term.boundVars().size() == 1 && term.arity() == 3) {
                var qv = term.boundVars().get(0);
                var lo = term.sub(0);
                var hi = term.sub(1);
                var cond = term.sub(2);
                return String.format("\\sum %s %s; %s <= %s <= %s; %s",
                        qv.sort().name(), qv.name().toString(),
                        translate(lo, pp, termBasePos, itype),
                        qv.name().toString(),
                        translate(hi, pp, termBasePos, itype),
                        translate(cond, pp, termBasePos, itype));
            }

            if (term.op().name().toString().equals("bprod") && term.boundVars().size() == 1 && term.arity() == 3) {
                var qv = term.boundVars().get(0);
                var lo = term.sub(0);
                var hi = term.sub(1);
                var cond = term.sub(2);
                return String.format("\\product %s %s; %s <= %s && %s < %s; %s",
                        qv.sort().name(), qv.name().toString(),
                        translate(lo, pp, termBasePos, itype),
                        qv.name().toString(),
                        qv.name().toString(),
                        translate(hi, pp, termBasePos, itype),
                        translate(cond, pp, termBasePos, itype));
            }

            if (term.op().name().toString().endsWith("::select")) {

                Term selectHeap = term.sub(0);
                Term selectBase = term.sub(1);
                Term selectSel = term.sub(2);


                if (selectBase.op() instanceof LocationVariable && selectBase.op().name().toString().equals("self") && selectSel.sort().name().toString().equals("Field")) {
                    var opstr = selectSel.op().toString();
                    if (opstr.contains("::$")) {
                        return "this." + opstr.substring(opstr.indexOf("::$") + 3);
                    } else {
                        return opstr;
                    }
                }

                if (selectBase.op() instanceof LocationVariable && selectSel.op().name().toString().equals("arr")) {
                    return String.format("%s[%s]", selectBase.op().name().toString(), translate(selectSel.sub(0), pp, termBasePos, itype));
                }

                if (selectSel.op() instanceof Function && selectSel.op().name().toString().endsWith("::<created>")) {
                    return String.format("\\created(%s)", selectBase.op().name().toString()); //TODO not valid JML
                }

            }

            //if (term.op().name().toString().equals("length") && term.op().sort(term.subs()).name().toString().equals("int")) {
            //    return translate(term.sub(0)) + ".length";
            //}

            if (term.op() instanceof Function && term.op().sort(term.subs()).name().toString().equals("Field")) {
                return term.op().toString();
            }

            if (term.op() instanceof Function && term.op().sort(term.subs()).name().toString().equals("Field")) {
                return term.op().toString();
            }

            if (term.op() == Junctor.TRUE) {
                return "true";
            }
            if (term.op() == Junctor.FALSE) {
                return "false";
            }
        }

        // all hope is lost - error out

        throw new TransformException("Failed to translate term (unsupported op): " + translateRaw(term, true));
    }

    private String bracketTranslate(Term base, Term child, InsPositionProvider pp, Integer basePos, InsertionType itype) throws TransformException, InternTransformException {
        if (needsBrackets(base, child)) {
            return "(" + translate(child, pp, basePos, itype) + ")";
        } else {
            return translate(child, pp, basePos, itype);
        }
    }

    private boolean needsBrackets(Term base, Term child) {
        // this is by far not exhaustive, but more brackets are not an error

        if (child.op() instanceof LocationVariable) return false;
        if (child.op().arity() == 0) return false;
        if (child.op() instanceof Function && child.op().name().toString().equals("Z")) return false;
        if (child.op() instanceof Function && bracketFuncs.containsKey(child.op().name().toString())) return false;
        if (child.op().name().toString().endsWith("::select")) return false;

        return true;
    }
}
