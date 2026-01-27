package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import org.key_project.prover.sequent.Sequent;
import org.key_project.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.extsourceview.Utils;

import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
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
            return methodPosition.getStartPosition().getLine() + 1;
        }
        if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return methodPosition.getStartPosition().getLine() + 1;
        }
        if (iterm.Type == InsertionType.ASSERT) {
            return methodPosition.getEndPosition().getLine();
        }
        if (iterm.Type == InsertionType.ASSIGNABLE) {
            return methodPosition.getEndPosition().getLine();
        }
        if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return methodPosition.getEndPosition().getLine();
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
    public Optional<Integer> GetTermHeapPosition(Sequent s, Term t, InsertionType itype) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() throws TransformException {
        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }

    @Override
    public Integer getLoopStartPos() throws TransformException, InternTransformException {
        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }

    @Override
    public boolean heapPosAreEqual(int p1, int p2) {
        return p1 == p2;
    }
}
