package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import org.key_project.extsourceview.Utils;
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
    private final Sequent sequent;

    private final boolean enableFallbackTranslation;
    private final boolean allowUnknownConstants;
    private final boolean manuallyTranslateLoopAssertions;

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


    public TermTranslator(URI fileUri, Services services, Sequent seq, boolean enableFallback, boolean allowUnknownConstants, boolean manuallyTranslateLoopAssertions) {
        this.fileUri = fileUri;
        this.svc = services;
        this.sequent = seq;
        this.enableFallbackTranslation = enableFallback;
        this.allowUnknownConstants = allowUnknownConstants;
        this.manuallyTranslateLoopAssertions = manuallyTranslateLoopAssertions;
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

    public String translate(InsertionTerm iterm, InsPositionProvider pp) throws TransformException, InternTransformException {

        var mpm = pp.getMethodPositionMap();
        var heaps = MovingPositioner.listHeaps(sequent, iterm.Term, true);
        var basePos = heaps.stream().map(p -> p.getLineNumber(mpm)).filter(Optional::isPresent).map(Optional::get).max(Comparator.comparingInt(p->p)).orElse(null);

        if (iterm.Type == InsertionType.ASSUME) {
            return "//@ assume " + translate(iterm.Term, pp, basePos, iterm.Type, true) + ";";
        } else if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return "//@ assume "+translate(iterm.Term, pp, basePos, iterm.Type, true)+  "; // (CAT-ERROR)";
        } else if (iterm.Type == InsertionType.ASSERT) {
            return "//@ assert " + translate(iterm.Term, pp, basePos, iterm.Type, true) + ";";
        } else if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return "//@ assert "+translate(iterm.Term, pp, basePos, iterm.Type, true)+"; //  (CAT-ERROR)";
        } else if (iterm.Type == InsertionType.ASSIGNABLE) {
            try {
                return "//@ assignable " + translateAssignable(iterm.Term) + "; //TODO";
            } catch (TransformException | InternTransformException e) {
                //TODO catch assignable-translate error here while its still WIP,
                //     this way we dont need continue-on-error if assignable-translation fails
                //     later simply remove this try-catch (then gets caught higher up)
                return "//@ assignable (ERROR); //TODO";
            }
        } else {
            throw new TransformException("Unknown value for InsertionType");
        }
    }

    public String translateSafe(InsertionTerm iterm, InsPositionProvider pp) {
        try {
            return translate(iterm, pp);
        } catch (TransformException | InternTransformException e) {
            return "//@ unknown (TRANSLATE-ERROR); //" + translateRaw(iterm.Term, true);
        }
    }

    public String translateSafe(Term term, InsertionType itype) {
        try {
            return translate(term, new DummyPositionProvider(), null, itype, false);
        } catch (TransformException | InternTransformException e) {
            return "";
        }
    }

    private boolean canTranslateDirectly(Term term, InsPositionProvider pp, Integer termBasePos) throws InternTransformException, TransformException {
        var origin = term.getOriginRef()
                .stream()
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP)
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL)
                .filter(p -> p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());

        var heaps = MovingPositioner.listHeaps(sequent, term, true);

        if (origin.size() == 1 && (termBasePos == null || (heaps.size() == 1 && heaps.get(0).getLineNumber(pp.getMethodPositionMap()).orElse(-1).equals(termBasePos)) || (heaps.size() == 0))) {
            OriginRef singleorig = origin.get(0);
            if (singleorig.SourceTerm != null && origin.get(0).hasFile()) {
                return origin.get(0).sourceString().filter(s -> !s.isEmpty()).isPresent();
            }
        }

        return false;
    }

    private String translate(Term term, InsPositionProvider pp, Integer termBasePos, InsertionType itype, boolean root) throws TransformException, InternTransformException {
        var origin = term.getOriginRef()
                .stream()
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP)
                .filter(p -> p.Type != OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL)
                .filter(p -> p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());

        if (termBasePos != null) {
            var posOfTerm = pp.GetTermHeapPosition(sequent, term, itype);

            if (posOfTerm.isPresent()) {
                var posOfTermVal = posOfTerm.get();

                if (!pp.heapPosAreEqual(posOfTermVal, termBasePos)) {
                    if (pp.heapPosAreEqual(pp.getOldPos(), posOfTermVal)) {
                        return "\\old(" + translate(term, pp, posOfTermVal, itype, false) + ")";
                    } else  {
                        return "\\old<"+posOfTerm.get()+">(" + translate(term, pp, posOfTermVal, itype, false) + ")";
                    }
                }
            }

        }

        var heaps = MovingPositioner.listHeaps(sequent, term, true);

        //TODO shouldn't we use pp.heapPosAreEqual here instead of directly comparing the line-numbers?
        if (origin.size() == 1 && (termBasePos == null || (heaps.size() == 1 && heaps.get(0).getLineNumber(pp.getMethodPositionMap()).orElse(-1).equals(termBasePos)) || (heaps.size() == 0))) {

            OriginRef singleorig = origin.get(0);

            // simple case - use origin directly

            if (singleorig.SourceTerm != null && origin.get(0).hasFile()) {
                var r = origin.get(0).sourceString();
                if (r.isEmpty()) {
                    throw new TransformException("Failed to get origin of term");
                }
                if (!r.get().isEmpty()) {
                    // can mostly happen with for loops (they have no proper origin, due to for-to-while conversion)
                    return r.get();
                }
            }

            // handle annoying special cases

            if ((singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP
                    || singleorig.Type == OriginRefType.LOOP_INITIALLYVALID_WELLFORMED
                    || singleorig.Type == OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED
                    || singleorig.Type == OriginRefType.LOOP_USECASE_WELLFORMED
                    || singleorig.Type == OriginRefType.OPERATION_PRE_WELLFORMED
                    || singleorig.Type == OriginRefType.OPERATION_POST_WELLFORMED
                    || singleorig.Type == OriginRefType.OPERATION_EXC_WELLFORMED)
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

            if ((singleorig.Type == OriginRefType.IMPLICIT_ENSURES_SELFINVARIANT
              || singleorig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT
              || singleorig.Type == OriginRefType.OPERATION_POST_SELFINVARIANT
              || singleorig.Type == OriginRefType.OPERATION_EXC_SELFINVARIANT)
                    && term.op().name().toString().equals("java.lang.Object::<inv>")
                    && (term.sub(1).op().name().toString().equals("self") || term.sub(1).op().name().toString().startsWith("self_"))) {
                return "\\invariant_for(this)";
            }

            if (term.op().name().toString().equals("java.lang.Object::<inv>")
                    && (term.sub(1).op().name().toString().equals("self") || term.sub(1).op().name().toString().startsWith("self_"))) {
                return "\\invariant_for("+translate(term.sub(1), pp, termBasePos, itype, false)+")";
            }

        }

        if (manuallyTranslateLoopAssertions && root) {

            // Directly Translate @assert <loop-invariant> with JML expression

            var originInvAfter = origin.stream().filter(p -> p.Type == OriginRefType.LOOP_BODYPRESERVEDINV_INVARIANT_AFTER).findFirst();
            if (originInvAfter.isPresent() && originInvAfter.get().hasFile()) {
                var r = originInvAfter.get().sourceString();
                if (r.isEmpty()) {
                    throw new TransformException("Failed to get origin of term");
                }
                if (!r.get().isEmpty()) {
                    // can mostly happen with for loops (they have no proper origin, due to for-to-while conversion)
                    return r.get();
                }
            }

            // Directly Translate @assert <loop-decreases> with JML expression

            var originDecreases = origin.stream().filter(p -> p.Type == OriginRefType.LOOP_BODYPRESERVEDINV_VARIANT).findFirst();
            if (originDecreases.isPresent() && term.op().name().toString().equals("prec") && term.arity() == 2) {
                var prec0 = term.sub(0);

                var realOriginDecreases = prec0.getOriginRef().stream().filter(p -> p.Type == OriginRefType.LOOP_BODYPRESERVEDINV_VARIANT).findFirst();
                if (realOriginDecreases.isPresent() && realOriginDecreases.get().hasFile()) {

                    var r = realOriginDecreases.get().sourceString();
                    if (r.isEmpty()) {
                        throw new TransformException("Failed to get origin of term");
                    }

                    var precHeaps = MovingPositioner.listHeaps(sequent, prec0, true);
                    int heapLine = precHeaps.stream().map(p -> p.getLineNumber(null).orElse(-1)).max(Integer::compare).orElse(-1);

                    if (heapLine < 0) {
                        //TODO this is kinda hacky, we need a better way to find the (heap) position of the current loop
                        var lsp = pp.getLoopStartPos();
                        if (lsp != null) heapLine = lsp;
                    }

                    if (!r.get().isEmpty()) {
                        if (heapLine > 0 ) {
                            return String.format("0 <= (%s) < \\old<%d>(%s)", r.get(), heapLine, r.get());
                        } else {
                            return String.format("0 <= (%s) < \\old(%s)", r.get(), r.get());
                        }
                    }
                }
            }

        }

        if (enableFallbackTranslation) {
            // ======= try to manually build the JML =======

            // special cases

            if (term.op().name().toString().equals("not")
                    && term.sub(0).op().name().toString().equals("equals")
                    && term.sub(0).arity() == 2
                    && !canTranslateDirectly(term.sub(0), pp, termBasePos)) {
                return String.format("%s != %s",
                        bracketTranslate(term.sub(0), term.sub(0).sub(0), pp, termBasePos, itype),
                        bracketTranslate(term.sub(0), term.sub(0).sub(1), pp, termBasePos, itype));
            }

            if (term.op().name().toString().equals("wellFormed") && term.arity() == 1 && term.sub(0).op().sort(term.sub(0).subs()).toString().equals("Heap")) {
                return "\\wellFormed("+term.sub(0).op().toString()+")"; // TODO not valid JML
            }

            if (term.op().name().toString().endsWith("::exactInstance") && term.arity() == 1) {
                return "\\exactInstance("+term.sub(0).op().toString()+")"; // TODO not valid JML
            }

            // Use OriginFuncNameMap

            if (term.op() instanceof Function && term.op().arity() == 0 && svc.getOriginFuncNameMap().has(term.op().name())) {
                return svc.getOriginFuncNameMap().get(term.op().name()).toString();
            }

            // ...

            if (term.op() instanceof LocationVariable && term.arity() == 0 && (term.op().name().toString().equals("self") || term.op().name().toString().startsWith("self_"))) {
                return "this";
            }

            if (term.op() instanceof LocationVariable && term.arity() == 0) {
                return term.op().name().toString();
            }

            if (term.op() instanceof Function && term.op().name().toString().equals("Z")) {
                return translateRaw(term, true);
            }

            if (term.op() instanceof Function && term.arity() == 0 && nullaryFuncs.containsKey(term.op().name().toString())) {
                return nullaryFuncs.get(term.op().name().toString());
            }

            if ((term.op() instanceof Function || term.op() instanceof AbstractSortedOperator) && inlineFuncs.containsKey(term.op().name().toString())) {

                // special case to simplify `a == true` and `true == a)`
                if (term.arity() == 2 && term.sub(1).op().arity() == 0 && term.sub(1).op().name().toString().equals("TRUE")) {
                    return translate(term.sub(0), pp, termBasePos, itype, false);
                }
                if (term.arity() == 2 && term.sub(0).op().arity() == 0 && term.sub(0).op().name().toString().equals("TRUE")) {
                    return translate(term.sub(1), pp, termBasePos, itype, false);
                }

                String fmt = inlineFuncs.get(term.op().name().toString());

                Object[] p = new String[term.arity()];
                for (int i = 0; i < term.arity(); i++) {
                    p[i] = bracketTranslate(term, term.sub(i), pp, termBasePos, itype);
                }
                return String.format(fmt, p);
            }

            if (term.op() instanceof Function && term.op().name().toString().equals("store")) {
                return translate(term.sub(2), pp, termBasePos, itype, false);
            }

            if (term.op() == Quantifier.ALL && term.boundVars().size() == 1 && term.arity() == 1) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("\\forall %s %s; %s", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype, false));
            }

            if (term.op() == Quantifier.EX && term.boundVars().size() == 1 && term.arity() == 1) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("\\exists %s %s; %s", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype, false));
            }

            if (term.op() instanceof Function && term.op().name().toString().equals("created")) {
                var qv = term.boundVars().get(0);
                var sub = term.sub(0);
                return String.format("(\\exists %s %s; %s)", qv.sort().name(), qv.name().toString(), translate(sub, pp, termBasePos, itype, false));
            }

            if (term.op().name().toString().equals("bsum") && term.boundVars().size() == 1 && term.arity() == 3) {
                var qv = term.boundVars().get(0);
                var lo = term.sub(0);
                var hi = term.sub(1);
                var cond = term.sub(2);
                return String.format("\\sum %s %s; %s <= %s < %s; %s",
                        qv.sort().name(), qv.name().toString(),
                        translate(lo, pp, termBasePos, itype, false),
                        qv.name().toString(),
                        translate(hi, pp, termBasePos, itype, false),
                        translate(cond, pp, termBasePos, itype, false));
            }

            if (term.op().name().toString().equals("bprod") && term.boundVars().size() == 1 && term.arity() == 3) {
                var qv = term.boundVars().get(0);
                var lo = term.sub(0);
                var hi = term.sub(1);
                var cond = term.sub(2);
                return String.format("\\product %s %s; %s <= %s && %s < %s; %s",
                        qv.sort().name(), qv.name().toString(),
                        translate(lo, pp, termBasePos, itype, false),
                        qv.name().toString(),
                        qv.name().toString(),
                        translate(hi, pp, termBasePos, itype, false),
                        translate(cond, pp, termBasePos, itype, false));
            }

            if (term.sort().name().toString().equals("Field")) {
                return translateField(term);
            }

            if (term.op().name().toString().endsWith("::select")) {

                Term selectHeap = term.sub(0);
                Term selectBase = term.sub(1);
                Term selectSel = term.sub(2);


                if (selectSel.op() instanceof Function && selectSel.op().name().toString().endsWith("::<created>")) {
                    return String.format("\\created(%s)", translate(selectBase, pp, termBasePos, itype, false)); //TODO not valid JML
                }

                if (selectBase.op() instanceof LocationVariable && (selectBase.op().name().toString().equals("self") || selectBase.op().name().toString().startsWith("self_")) && selectSel.sort().name().toString().equals("Field")) {
                    return translate(selectSel, pp, termBasePos, itype, false);
                }


                if ((selectBase.op() instanceof LocationVariable || selectBase.sort().name().toString().endsWith("[]")) && selectSel.op().name().toString().equals("arr")) {
                    return String.format("%s[%s]", translate(selectBase, pp, termBasePos, itype, false), translate(selectSel.sub(0), pp, termBasePos, itype, false));
                }

            }

            if (term.op().name().toString().equals("java.lang.Object::<inv>")
                    && (term.sub(1).op().name().toString().equals("self") || term.sub(1).op().name().toString().startsWith("self_"))) {
                return "\\invariant_for("+translate(term.sub(1), pp, termBasePos, itype, false)+")";
            }

            if (term.op().name().toString().equals("if-then-else") && term.arity() == 3) {
                var ite_cond = translate(term.sub(0), pp, termBasePos, itype, false);
                var ite_true = translate(term.sub(1), pp, termBasePos, itype, false);
                var ite_fals = translate(term.sub(2), pp, termBasePos, itype, false);
                if (ite_true.equals(ite_fals)) return ite_true;
                return String.format("(%s) ? (%s) : (%s)", ite_cond, ite_true, ite_fals);
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

            if (term.op() instanceof Function && term.arity() == 0 && allowUnknownConstants) {
                return term.op().toString();
            }

            if (term.op() instanceof LogicVariable && term.arity() == 0) {
                return term.op().toString();
            }
        }

        // all hope is lost - error out

        throw new TransformException("Failed to translate term (unsupported op '"+term.op().name()+"')", translateRaw(term, true));
    }

    private String bracketTranslate(Term base, Term child, InsPositionProvider pp, Integer basePos, InsertionType itype) throws TransformException, InternTransformException {
        if (needsBrackets(base, child)) {
            return "(" + translate(child, pp, basePos, itype, false) + ")";
        } else {
            return translate(child, pp, basePos, itype, false);
        }
    }

    private boolean needsBrackets(Term base, Term child) {
        // this is by far not exhaustive, but more brackets are not an error

        if (child.op() instanceof LocationVariable) return false;
        if (child.op().arity() == 0) return false;
        if (child.op() instanceof Function && child.op().name().toString().equals("Z")) return false;
        if (child.op().name().toString().endsWith("::select")) return false;

        return true;
    }

    private String translateField(Term term) {
        var opstr = term.op().toString();
        if (opstr.contains("::$")) {
            return /*"this." + */ opstr.substring(opstr.indexOf("::$") + 3);
        } else {
            return opstr;
        }
    }

    private String translateAssignable(Term term) throws TransformException, InternTransformException {

        var fieldLoop = term;
        if (fieldLoop.op() != Quantifier.ALL || fieldLoop.arity() != 1 || fieldLoop.boundVars().size() != 1 || !fieldLoop.boundVars().get(0).sort().name().toString().equals("Field")) {
            throw new TransformException("assignable term@1 must be \\forall(Fields)");
        }

        var fieldName = fieldLoop.boundVars().get(0).name().toString();

        var objectLoop = term.sub(0);
        if (objectLoop.op() != Quantifier.ALL || objectLoop.arity() != 1 || objectLoop.boundVars().size() != 1 || !objectLoop.boundVars().get(0).sort().name().toString().equals("java.lang.Object")) {
            throw new TransformException("assignable term@2 must be \\forall(Objects)");
        }

        var objName = objectLoop.boundVars().get(0).name().toString();

        var assignableConditions = Utils.splitFormula(objectLoop.sub(0), Junctor.OR);

        java.util.function.Function<Term, Boolean> isObjEqualsSelf = (Term t) -> {
            if (t.op() != Equality.EQUALS) return false;
            if (t.arity() != 2) return false;
            var sub1 = t.sub(0);
            var sub2 = t.sub(1);
            if (!sub1.sort().name().toString().equals("java.lang.Object")) return false;
            if (!sub1.op().name().toString().equals(objName)) return false;
            if (!(sub2.op().name().toString().equals("self") || sub2.op().name().toString().startsWith("self_"))) return false;

            return true;
        };

        java.util.function.Function<Term, Boolean> isFieldEqualsFunc = (Term t) -> {
            if (t.op() != Equality.EQUALS) return false;
            if (t.arity() != 2) return false;
            var sub1 = t.sub(0);
            var sub2 = t.sub(1);
            if (!sub1.sort().name().toString().equals("Field")) return false;
            if (!sub1.op().name().toString().equals(fieldName)) return false;
            if (!(sub2.arity() == 0 && sub2.sort().name().toString().equals("Field") )) return false;

            return true;
        };

        java.util.function.Function<Term, Boolean> isObjNotEqualsNull = (Term t) -> {
            if (t.op() != Junctor.NOT) return false;
            var sub = t.sub(0);
            if (sub.op() != Equality.EQUALS) return false;
            if (sub.arity() != 2) return false;
            var sub1 = sub.sub(0);
            var sub2 = sub.sub(1);
            if (!sub1.sort().name().toString().equals("java.lang.Object")) return false;
            if (!sub1.op().name().toString().equals(objName)) return false;
            if (!sub2.op().name().toString().equals("null")) return false;

            return true;
        };

        java.util.function.Function<Term, Boolean> isObjNotCreated = (Term t) -> {
            if (t.op() != Junctor.NOT) return false;
            var sub = t.sub(0);
            if (sub.op() != Equality.EQUALS) return false;
            if (sub.arity() != 2) return false;
            var sub1 = sub.sub(0);
            if (!(sub1.op().name().toString().equals("boolean::select") && sub1.arity() == 3)) return false;
            var sub2 = sub.sub(1);
            if (!sub2.op().name().toString().equals("TRUE")) return false;
            var csub2 = sub1.sub(1);
            var csub3 = sub1.sub(2);
            if (!csub2.sort().name().toString().equals("java.lang.Object")) return false;
            if (!csub2.op().name().toString().equals(objName)) return false;
            if (!csub3.op().name().toString().equals("java.lang.Object::<created>")) return false;

            return true;
        };

        java.util.function.Function<Term, Boolean> isFieldEqualsSelf = (Term t) -> {
            if (t.op() != Equality.EQUALS) return false;
            if (t.arity() != 2) return false;
            var sub1 = t.sub(0);
            var sub2 = t.sub(1);
            if (!(sub1.op().name().toString().endsWith("::select") && sub1.arity() == 3)) return false;
            if (!(sub2.op().name().toString().endsWith("::select") && sub2.arity() == 3)) return false;
            var o1 = sub1.sub(1);
            var f1 = sub1.sub(2);
            var o2 = sub2.sub(1);
            var f2 = sub2.sub(2);
            if (!(o1.sort().name().toString().equals("java.lang.Object") && o1.op().name().toString().equals(objName))) return false;
            if (!(f1.sort().name().toString().equals("Field") && f1.op().name().toString().equals(fieldName))) return false;
            if (!(o2.sort().name().toString().equals("java.lang.Object") && o2.op().name().toString().equals(objName))) return false;
            if (!(f2.sort().name().toString().equals("Field") && f2.op().name().toString().equals(fieldName))) return false;
            return true;
        };

        java.util.function.Function<Term, Boolean> isObjectEqualsVar = (Term t) -> {
            if (t.op() != Equality.EQUALS) return false;
            if (t.arity() != 2) return false;
            var sub1 = t.sub(0);
            var sub2 = t.sub(1);
            if (!sub1.op().name().toString().equals(objName)) return false;
            if (!(sub2.op().name().toString().endsWith("::select") && sub2.arity() == 3)) return false;
            var ss = sub2.sub(1);
            var vv = sub2.sub(2);
            if (!(vv.sort().name().toString().equals("Field"))) return false;
            return true;
        };

        var assignableVariables = new ArrayList<String>();

        var notCreatedCond = false;
        var unchangedCond = false;

        for (var cond : assignableConditions) {

            // o.f@[...] == o.f@[...]
            if (isFieldEqualsSelf.apply(cond)) {
                unchangedCond = true;
                continue;
            }

            // o == $
            if (isObjectEqualsVar.apply(cond)) {
                assignableVariables.add(translateField(cond.sub(1).sub(2)) + "[*]");
                continue;
            }

            if (cond.op() != Junctor.AND || cond.arity() != 2) {
                throw new TransformException("assignable term '"+cond.toString()+"' must be and($, $)");
            }

            var t1 = cond.sub(0);
            var t2 = cond.sub(1);

            // ( o == self ) && ( f == $ )
            if (isObjEqualsSelf.apply(t1) && isFieldEqualsFunc.apply(t2)) {
                assignableVariables.add(translateField(t2.sub(1)));
                continue;
            }

            // ( f == $ ) && ( o == self )
            if (isObjEqualsSelf.apply(t2) && isFieldEqualsFunc.apply(t1)) {
                assignableVariables.add(translateField(t1.sub(1)));
                continue;
            }

            // ( o != null ) && ( created(o) != true )
            if (isObjNotEqualsNull.apply(t1) && isObjNotCreated.apply(t2)) {
                notCreatedCond = true;
                continue;
            }

            // ( created(o) != true ) && ( o != null )
            if (isObjNotEqualsNull.apply(t2) && isObjNotCreated.apply(t1)) {
                notCreatedCond = true;
                continue;
            }

            throw new TransformException("assignable term '"+cond.toString()+"' cannot be categorized");
        }

        if (!unchangedCond) {
            throw new TransformException("assignable cannot be translated (missing o.f == o.f condition)");
        }

        if (!notCreatedCond) {
            throw new TransformException("assignable cannot be translated (missing !created(o) condition)");
        }

        return "[ " + String.join(", ", assignableVariables) + " ]";
    }
}
