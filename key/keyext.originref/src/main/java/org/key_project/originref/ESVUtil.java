package org.key_project.originref;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.IOUtil;

import javax.annotation.Nonnull;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

public class ESVUtil {

    public static String readFile(@Nonnull KeYMediator mediator, URI u) throws IOException {
        Proof proof = mediator.getSelectedProof();
        FileRepo repo = proof.getInitConfig().getFileRepo();
        try (InputStream is = repo.getInputStream(u.toURL())) {
            return IOUtil.readFrom(is);
        }
    }

    public static List<Term> splitAnd(SequentFormula sfv)  {
        return splitFormula(sfv.formula(), Junctor.AND);
    }

    public static List<Term> splitOr(SequentFormula sfv)  {
        return splitFormula(sfv.formula(), Junctor.OR);
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

    public static String TermToString(Term t, Services svc) throws IOException {
        //return t.toString();

        var ni = new NotationInfo();

        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(), ni, svc);
        ni.refresh(svc, true, false);

        t = removeLabelRecursive(svc.getTermFactory(), t);

        printer.printTerm(t);

        var v = printer.toString();

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

        String r = "";
        for (int i = lineStart; i <= lineEnd; i++) {
            if (i-1 < lines.size()) r += lines.get(i-1)+"\n";
        }
        return r;
    }

    public static Term getParentWithOriginRef(PosInSequent pos) {
        PosInOccurrence poc = pos.getPosInOccurrence();
        while (true) {
            Term t = poc.subTerm();
            java.util.List<OriginRef> to = t.getOriginRef().stream().collect(Collectors.toList());
            if (to.size() == 0) {
                if (poc.isTopLevel()) return t;
                poc = poc.up();
                continue;
            }
            return t;
        }
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

}
