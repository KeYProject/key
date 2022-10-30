package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class Utils {

    public static String TermToOrigString(Term t, Services svc) {
        OriginRef or = t.getOriginRef();
        if (or == null) {
            return "";
        }
        return or.sourceString();
    }

    public static String TermToString(Term t, Services svc, boolean singleLine) throws IOException {
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

        if (singleLine) v = v.replaceAll("\\r", "").replaceAll("\\n", " ");

        return v;
    }

    public static Term removeLabelRecursive(TermFactory tf, Term term) {
        // Update children
        List<Term> newSubs = new LinkedList<>();
        for (Term oldSub : term.subs()) {
            newSubs.add(removeLabelRecursive(tf, oldSub));
        }

        return tf.createTerm(term.op(), new ImmutableArray<>(newSubs), term.boundVars(), term.javaBlock(), null, term.getOriginRef());
    }

    public static String getLines(@Nonnull KeYMediator mediator, String file, int lineStart, int lineEnd) throws URISyntaxException, IOException {
        List<String> lines = Files.readAllLines(Path.of(file));

        StringBuilder r = new StringBuilder();
        for (int i = lineStart; i <= lineEnd; i++) {
            if (i-1 < lines.size()) r.append(lines.get(i - 1)).append("\n");
        }
        return r.toString();
    }

    public static Term getParentWithOriginRef(PosInSequent pos, boolean atom, boolean returnNullOnTopLevel) {
        PosInOccurrence poc = pos.getPosInOccurrence();
        while (true) {
            Term t = poc.subTerm();
            if (t.getOriginRef() != null && (!atom || t.getOriginRef().IsAtom)) {
                return t;
            }

            if (poc.isTopLevel()) return returnNullOnTopLevel ? null : t;
            poc = poc.up();
        }
    }

    public static ArrayList<OriginRef> getSubOriginRefs(Term term, boolean includeSelf, boolean onlyAtoms) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            if (term.getOriginRef() != null && (!onlyAtoms || term.getOriginRef().IsAtom)) r.add(term.getOriginRef());
        }

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                if (t.getOriginRef() != null && (!onlyAtoms || t.getOriginRef().IsAtom)) r.add(t.getOriginRef());
                r.addAll(getSubOriginRefs(t, false, onlyAtoms));
            }
        }

        return r;
    }

    public static String safeSubstring(String str, int start, int end) {
        start = Math.max(start, 0);
        end = Math.min(end, str.length());

        return str.substring(start, end);
    }
}
