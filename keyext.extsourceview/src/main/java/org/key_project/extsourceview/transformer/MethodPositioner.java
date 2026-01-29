package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import org.key_project.prover.sequent.Sequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;
import java.util.Optional;

/**
 * Implements the 'Method' Positioning strategy for InsertionTerms
 * The terms get written simply at the start and end of the method
 */
public class MethodPositioner extends InsPositionProvider {

    private final URI fileUri;

    public MethodPositioner(URI fileUri, Services svc, Proof proof, Node node) {
        super(svc, proof, node);

        this.fileUri = fileUri;
    }

    private int getLine(InsertionTerm iterm) throws TransformException, InternTransformException {
        var methodPosition = getMethodPositionMap();

        if (iterm.Type == InsertionType.ASSUME) {
            return methodPosition.getStartPosition().line() + 1;
        }
        if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return methodPosition.getStartPosition().line() + 1;
        }
        if (iterm.Type == InsertionType.ASSERT) {
            return methodPosition.getEndPosition().line();
        }
        if (iterm.Type == InsertionType.ASSIGNABLE) {
            return methodPosition.getEndPosition().line();
        }
        if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return methodPosition.getEndPosition().line();
        }
        throw new InternTransformException("unknown InsertionTerm.Type");

    }

    @Override
    public InsertionPosition getPosition(Sequent s, InsertionTerm iterm) throws TransformException, InternTransformException {
        var line = getLine(iterm);
        var indent = getLineIndent(fileUri, line);

        return new InsertionPosition(line, line, indent);
    }

    @Override
    public Optional<Integer> getTermHeapPosition(Sequent s, JTerm t, InsertionType itype) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() throws TransformException {
        return getMethodPositionMap().getStartPosition().line() + 1;
    }

    @Override
    public Integer getLoopStartPos() throws TransformException, InternTransformException {
        return getMethodPositionMap().getStartPosition().line() + 1;
    }

    @Override
    public boolean heapPosAreEqual(int p1, int p2) {
        return p1 == p2;
    }
}
