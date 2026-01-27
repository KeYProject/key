package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import org.key_project.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.key_project.extsourceview.transformer.HeapReference;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A set of utility functions for this plugin
 */
public class Utils {

    public static String getLines(URI file, int lineStart, int lineEnd) throws IOException {
        List<String> lines = Files.readAllLines(Path.of(file));

        StringBuilder r = new StringBuilder();
        for (int i = lineStart; i <= lineEnd; i++) {
            if (i - 1 < lines.size())
                r.append(lines.get(i - 1)).append("\n");
        }
        return r.toString();
    }

    public static String getLines(String file, int lineStart, int lineEnd) throws URISyntaxException, IOException {
        List<String> lines = Files.readAllLines(Path.of(file));

        StringBuilder r = new StringBuilder();
        for (int i = lineStart; i <= lineEnd; i++) {
            if (i - 1 < lines.size())
                r.append(lines.get(i - 1)).append("\n");
        }
        return r.toString();
    }

    public static Term getParentWithOriginRef(PosInSequent pos, boolean atom, boolean returnNullOnTopLevel) {
        PosInOccurrence poc = pos.getPosInOccurrence();
        while (true) {
            Term t = poc.subTerm();
            if (t.getOriginRef().stream().anyMatch(p -> !atom || p.isAtom())) {
                return t;
            }

            if (poc.isTopLevel())
                return returnNullOnTopLevel ? null : t;
            poc = poc.up();
        }
    }

    public static ArrayList<OriginRef> getSubOriginRefs(Term term, boolean includeSelf, boolean onlyAtoms) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            r.addAll(term.getOriginRef().stream().filter(p -> !onlyAtoms || p.isAtom()).collect(Collectors.toList()));
        }

        for (Term t : term.subs()) {
            r.addAll(t.getOriginRef().stream().filter(p -> !onlyAtoms || p.isAtom()).collect(Collectors.toList()));
            r.addAll(getSubOriginRefs(t, false, onlyAtoms));
        }

        return r;
    }

    public static String safeSubstring(String str, int start, int end) {
        start = Math.max(start, 0);
        end = Math.min(end, str.length());

        return str.substring(start, end);
    }

    public static List<Term> splitFormula(Term f, Operator j)  {
        var r = new ArrayList<Term>();

        if (f.op() == j) {
            r.addAll(splitFormula(f.sub(0), j));
            r.addAll(splitFormula(f.sub(1), j));
        } else {
            r.add(f);
        }

        return r;
    }
}
