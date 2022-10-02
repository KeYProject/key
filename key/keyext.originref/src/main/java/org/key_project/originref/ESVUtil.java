package org.key_project.originref;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.Pair;
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

        printer.printTerm(t);

        var v = printer.toString();

        v = v.replaceAll("\r", "").
                replaceAll("\n", " ").
                replaceAll("\\s\\s+", " ").
                replaceAll("<<SC, origin\\(.*?\\)>>", "").
                replaceAll("<<origin\\(.*?\\)>>", "").
                replaceAll("<<impl>>", "");

        return v;
    }

    public static LinkedList<Pair<Node, PositionInfo>> constructLinesSet(Node node) {
        LinkedList<Pair<Node, PositionInfo>> list = new LinkedList<>();

        if (node == null) {
            return null;
        }

        Node cur = node;

        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                addPosToList(joinPositionsRec(activeStatement), list, cur);
            }
            cur = cur.parent();

        } while (cur != null);

        return list;
    }

    private static void addPosToList(
            PositionInfo pos, LinkedList<Pair<Node, PositionInfo>> list, Node node) {
        if (pos != null
                && !pos.equals(PositionInfo.UNDEFINED) && pos.startEndValid()
                && pos.getURI() != null) {
            list.addLast(new Pair<>(node, pos));
            node.proof().lookup(ProofJavaSourceCollection.class).addRelevantFile(pos.getURI());
        }
    }

    /**
     * Joins all PositionInfo objects of the given SourceElement and its children.
     * @param se the given SourceElement
     * @return a new PositionInfo starting at the minimum of all the contained positions and
     * ending at the maximum position
     */
    private static PositionInfo joinPositionsRec(SourceElement se) {
        if (se instanceof NonTerminalProgramElement) {
            if (se instanceof If
                    || se instanceof Then
                    || se instanceof Else) { // TODO: additional elements, e.g. code inside if
                return PositionInfo.UNDEFINED;
            }

            NonTerminalProgramElement ntpe = (NonTerminalProgramElement)se;
            PositionInfo pos = se.getPositionInfo();

            for (int i = 0; i < ntpe.getChildCount(); i++) {
                ProgramElement pe2 = ntpe.getChildAt(i);
                pos = PositionInfo.join(pos, joinPositionsRec(pe2));
            }
            return pos;
        } else {
            return se.getPositionInfo();
        }
    }

    public static String getLines(@Nonnull KeYMediator mediator, String file, int lineStart, int lineEnd) throws URISyntaxException, IOException {

        List<String> lines = Files.readAllLines(Path.of(file));

        String r = "";
        for (int i = lineStart; i <= lineEnd; i++) {
            if (i+1 < lines.size()) r += lines.get(i+1)+"\n";
        }
        return r;
    }
}
