package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import org.key_project.prover.sequent.Sequent;
import org.key_project.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

/**
 * abstract base class for PositionProvied
 * A PositionProvider calculates the position where an InsertionTerm ends up in the SourceView
 */
public abstract class InsPositionProvider {

    public static class InsertionPosition {
        public final int Line;
        public final int HeapLine;
        public final int Indentation;

        public InsertionPosition(int line, int heapLine, int indent) {
            Line        = line;
            HeapLine    = heapLine;
            Indentation = indent;
        }
    }

    protected final Services svc;
    protected final Proof proof;
    protected final Sequent sequent;
    protected final Node node;

    public InsPositionProvider(Services svc, Proof proof, Node node) {
        this.svc = svc;
        this.proof = proof;
        this.sequent = (node == null) ? null : node.sequent();
        this.node = node;
    }

    public PositionInfo getMethodPositionMap() throws TransformException {

        ContractPO contractPO = svc.getSpecificationRepository().getPOForProof(proof);

        if (!(contractPO instanceof FunctionalOperationContractPO)) {
            throw new TransformException("Can only work on functional contracts");
        }

        FunctionalOperationContractPO funContractPO = (FunctionalOperationContractPO) contractPO;

        FunctionalOperationContract contract = funContractPO.getContract();

        IProgramMethod progrMethod = contract.getTarget();

        PositionInfo pos = progrMethod.getPositionInfo();

        return pos;
    }

    private static int getIndent(String str) {
        var indent = 0;
        while (str.length() > 0) {
            if (str.charAt(0) == ' ') {
                indent++;
            } else if (str.charAt(0) == '\t') {
                indent+=4;
            } else {
                return indent;
            }
            str = str.substring(1);
        }
        return indent;
    }

    public int getLineIndent(URI fileUri, int line) throws InternTransformException {
        if (fileUri == null) {
            return 0;
        }

        try {
            List<String> lines = Files.readAllLines(Path.of(fileUri));

            String before = null;
            for (int i = line-2; 0 <= i && i < lines.size(); i--) {
                var strline = lines.get(i);
                if (strline.trim().isEmpty()) continue;

                before = strline;
                break;
            }

            String after = null;
            for (int i = line-1; 0 <= i && i < lines.size(); i++) {
                var strline = lines.get(i);
                if (strline.trim().isEmpty()) continue;

                after = strline;
                break;
            }

            if (before == null && after == null) return 0;

            if (after == null) return getIndent(before);

            if (before == null) return getIndent(after);

            var indentBefore = getIndent(before);
            var indentAfter = getIndent(after);

            if (indentBefore == indentAfter) return indentBefore;

            return Math.max(indentBefore, indentAfter);

        } catch (IOException e) {
            throw new InternTransformException("Failed to get line-indent", e);
        }
    }

    public abstract InsertionPosition getPosition(Sequent s, InsertionTerm term) throws TransformException, InternTransformException;

    public abstract Optional<Integer> GetTermHeapPosition(Sequent s, Term t, InsertionType itype);

    public abstract Integer getOldPos() throws TransformException;

    public abstract Integer getLoopStartPos() throws TransformException, InternTransformException;

    public abstract boolean heapPosAreEqual(int p1, int p2);
}
