package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;

public class MethodPositioner extends InsPositionProvider {

    public MethodPositioner(Services svc, Proof proof, Node node) {
        super(svc, proof, node);
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
    public InsertionPosition getPosition(URI fileUri, InsertionTerm iterm) throws TransformException, InternTransformException {
        var line = getLine(iterm);
        var indent = getLineIndent(fileUri, line);

        return new InsertionPosition(line, indent);
    }
}
