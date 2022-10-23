package org.key_project.extsourceview;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

public class ESVBuilder {

    public static ESVInsertionSet extractParts(TermBuilder tb, Sequent sequent) {

        var ante = sequent.antecedent().asList().toList();
        var succ = sequent.succedent().asList().toList();

        var extInsertions = new ArrayList<InsertionTerm>();

        // all antecedents become asserts
        for (var sf: ante) {
            var t = sf.formula();

            if (!t.containsJavaBlockRecursive() && isExplicitRequires(t)) {
                extInsertions.add(new InsertionTerm(InsertionType.REQUIRES_EXPLICT, t));
                continue;
            }

            if (!t.containsJavaBlockRecursive() && isImplicitRequires(t)) {
                extInsertions.add(new InsertionTerm(InsertionType.REQUIRES_IMPLICT, t));
                continue;
            }

            //TODO fail if we can't identify a term (or ignore?)
        }

        int realSuccTerms = 0;

        // all assumes are either asserts after [notLeft] or java+<assumes>
        for (var sf: succ) {

            var t = sf.formula();

            // an requires after [notLeft]
            if (isExplicitRequires(t)) {
                extInsertions.add(new InsertionTerm(InsertionType.REQUIRES_EXPLICT, tb.not(t)));
                continue;
            }

            // an requires after [notLeft]
            if (isImplicitRequires(t)) {
                extInsertions.add(new InsertionTerm(InsertionType.REQUIRES_IMPLICT, tb.not(t)));
                continue;
            }

            if (t.containsJavaBlockRecursive()) { // TODO: remove this, we dont actually support modalities for now
                var ins = extractSuccedent(t);
                if (ins.size() > 0) {
                    extInsertions.addAll(ins);
                    realSuccTerms++;
                }
                continue;
            }

            {
                var ins = extractSuccedent(t);
                if (ins.size() > 0) {
                    extInsertions.addAll(ins);
                    realSuccTerms++;
                }
                continue;

            }

            //TODO fail if we can't identify a term (or ignore?)

        }

        //TODO fail if multiple succ blocks (?)
        //     or return some kind of either-or thingy

        return new ESVInsertionSet(ImmutableList.fromList(extInsertions));
    }

    public static List<InsertionTerm> extractSuccedent(Term t) {

        // simple case
        if (isExplicitEnsures(t)) {
            return Collections.singletonList(new InsertionTerm(InsertionType.ENSURES_EXPLICT, t));
        }

        // simple case
        if (isImplicitEnsures(t)) {
            return Collections.singletonList(new InsertionTerm(InsertionType.ENSURES_IMPLICT, t));
        }

        if (t.op() == UpdateApplication.UPDATE_APPLICATION) {
            return extractSuccedent(t.sub(1)); //TODO handle updates
        }

        if (t.op() == Modality.DIA && !t.javaBlock().isEmpty()) {
            var result = new ArrayList<InsertionTerm>();
            for (var ensTerm: splitFormula(t.sub(0), Junctor.AND)) {
                if (isExplicitEnsures(ensTerm)) {
                    result.add(new InsertionTerm(InsertionType.ENSURES_EXPLICT, ensTerm));
                } else if (isImplicitEnsures(ensTerm)) {
                    result.add(new InsertionTerm(InsertionType.ENSURES_IMPLICT, ensTerm));
                } else {
                    result.add(new InsertionTerm(InsertionType.ENSURES_UNKNOWN, ensTerm)); //TOOD what do here?
                }
            }
            return result;
        }

        {
            var result = new ArrayList<InsertionTerm>();
            for (var ensTerm : splitFormula(t, Junctor.AND)) {
                if (isExplicitEnsures(ensTerm)) {
                    result.add(new InsertionTerm(InsertionType.ENSURES_EXPLICT, ensTerm));
                } else if (isImplicitEnsures(ensTerm)) {
                    result.add(new InsertionTerm(InsertionType.ENSURES_IMPLICT, ensTerm));
                } else {
                    result.add(new InsertionTerm(InsertionType.ENSURES_UNKNOWN, ensTerm)); //TOOD what do here?
                }
            }
            return result;
        }

    }

    public static boolean isExplicitRequires(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [REQUIRES_IMPLICT] | [REQUIRES]
        // at least one must be [REQUIRES]

        var explicitRefs = 0;
        for(var o: origin) {
            if (o.Type == OriginRefType.TERM) continue;

            if (o.Type != OriginRefType.REQUIRES && o.Type != OriginRefType.REQUIRES_IMPLICT) {
                return false;
            }

            if (o.Type == OriginRefType.REQUIRES) {
                explicitRefs++;
            }
        }

        return explicitRefs > 0;
    }

    public static boolean isImplicitRequires(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [REQUIRES_IMPLICT]

        int implicitRefs = 0;

        for(var o: origin) {
            if (o.Type == OriginRefType.TERM) continue;

            if (o.Type == OriginRefType.REQUIRES_IMPLICT) {
                implicitRefs++;
            } else {
                return false;
            }
        }

        return implicitRefs > 0;
    }

    public static boolean isExplicitEnsures(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [ENSURES_IMPLICT] | [ENSURES]
        // at least one must be [ENSURES]

        var explicitRefs = 0;
        for(var o: origin) {
            if (o.Type == OriginRefType.TERM) continue;

            if (o.Type != OriginRefType.ENSURES && o.Type != OriginRefType.ENSURES_IMPLICT) {
                return false;
            }

            if (o.Type == OriginRefType.ENSURES) {
                explicitRefs++;
            }
        }

        return explicitRefs > 0;
    }

    public static boolean isImplicitEnsures(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [ENSURES_IMPLICT]

        int implicitRefs = 0;

        for(var o: origin) {
            if (o.Type == OriginRefType.TERM) continue;

            if (o.Type == OriginRefType.ENSURES_IMPLICT) {
                implicitRefs++;
            } else {
                return false;
            }
        }

        return implicitRefs > 0;
    }

    public static ArrayList<OriginRef> getSubOriginRefs(Term term, boolean includeSelf) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            for (OriginRef o: term.getOriginRef()) r.add(o);
        }

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                for (OriginRef o: t.getOriginRef()) r.add(o);
                r.addAll(getSubOriginRefs(t, false));
            }
        }

        return r;
    }

    //TODO remove me
    public static String TermToString(Term t, Services svc) throws IOException {
        //return t.toString();

        if (svc == null) {
            svc = new Services(AbstractProfile.getDefaultProfile());
        }

        var ni = new NotationInfo();

        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(), ni, svc);
        ni.refresh(svc, true, false);

        t = removeLabelRecursive(svc.getTermFactory(), t);

        printer.printTerm(t);

        var v = printer.toString();

        return v.replaceAll("\r", "").replaceAll("\n", " ").trim();
    }

    //TODO remove me
    public static Term removeLabelRecursive(TermFactory tf, Term term) {
        // Update children
        List<Term> newSubs = new LinkedList<>();
        for (Term oldSub : term.subs()) {
            newSubs.add(removeLabelRecursive(tf, oldSub));
        }

        return tf.createTerm(term.op(), new ImmutableArray<>(newSubs), term.boundVars(), term.javaBlock(), null, term.getOriginRef());
    }

    public static List<Term> splitFormula(Term f, Operator j)  {
        var r = new ArrayList<Term>();

        if (f.op() == j) {

            for (var f0: splitFormula(f.sub(0), j)) {
                r.add(f0);
            }
            for (var f1: splitFormula(f.sub(1), j)) {
                r.add(f1);
            }

        } else {
            r.add(f);
        }


        return r;
    }

}
