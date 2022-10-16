package org.key_project.extsourceview;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
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
import java.util.LinkedList;
import java.util.List;

public class ESVBuilder {

    public static ESVInsertionSet extractParts(TermBuilder tb, Sequent sequent) {

        var ante = sequent.antecedent().asList().toList();
        var succ = sequent.succedent().asList().toList();

        var assumes = new ArrayList<InsertionTerm>();
        var asserts = new ArrayList<InsertionTerm>();

        // all antecedents become asserts
        for (var sf: ante) {
            var t = sf.formula();

            if (!t.containsJavaBlockRecursive() && isExplicitRequires(t)) {
                assumes.add(new InsertionTerm(InsertionType.REQUIRES_EXPLICT, t));
                continue;
            }

            if (!t.containsJavaBlockRecursive() && isImplicitRequires(t)) {
                assumes.add(new InsertionTerm(InsertionType.REQUIRES_IMPLICT, t));
                continue;
            }

            //TODO fail if we can't identify a term (or ignore?)
        }

        int realSuccTerms = 0;

        // all assumes are either asserts after [notLeft] or java+<assumes>
        for (var sf: succ) {

            var t = sf.formula();

            if (!t.containsJavaBlockRecursive() && isExplicitRequires(t)) {
                assumes.add(new InsertionTerm(InsertionType.REQUIRES_EXPLICT, tb.not(t)));
                continue;
            }

            if (!t.containsJavaBlockRecursive() && isImplicitRequires(t)) {
                assumes.add(new InsertionTerm(InsertionType.REQUIRES_IMPLICT, tb.not(t)));
                continue;
            }

            if (!t.containsJavaBlockRecursive() && isExplicitEnsures(t)) {
                asserts.add(new InsertionTerm(InsertionType.ENSURES_EXPLICT, t));
                realSuccTerms++;
            }

            if (!t.containsJavaBlockRecursive() && isImplicitEnsures(t)) {
                asserts.add(new InsertionTerm(InsertionType.ENSURES_IMPLICT, t));
                realSuccTerms++;
            }

            if (t.javaBlock() != null) {
                //TODO impl
                //TODO what about update ( java-block ( ... ) )
                //asserts.add(t); // add stuff after java-block
                realSuccTerms++;
            }

            //TODO fail if we can't identify a term (or ignore?)

        }

        //TODO fail if multiple succ blocks (?)
        //     or return some kind of either-or thingy

        return new ESVInsertionSet(ImmutableList.fromList(assumes), ImmutableList.fromList(asserts));
    }

    public static boolean isExplicitRequires(Term term) {
        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [REQUIRES_IMPLICT] | [REQUIRES]
        // at least one must be [REQUIRES]

        var explicitRefs = 0;
        for(var o: origin) {
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
        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [REQUIRES_IMPLICT]

        for(var o: origin) {
            if (o.Type != OriginRefType.REQUIRES_IMPLICT) {
                return false;
            }
        }

        return true;
    }

    public static boolean isExplicitEnsures(Term term) {
        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [ENSURES_IMPLICT] | [ENSURES]
        // at least one must be [ENSURES]

        var explicitRefs = 0;
        for(var o: origin) {
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
        var origin = term.getOriginRef();
        if (origin.size() == 0) return false;

        // all origin-refs must be [ENSURES_IMPLICT]

        for(var o: origin) {
            if (o.Type != OriginRefType.ENSURES_IMPLICT) {
                return false;
            }
        }

        return true;
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
}
