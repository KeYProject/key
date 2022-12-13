package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;
import java.util.Optional;

public class DummyPositionProvider extends InsPositionProvider {
    public DummyPositionProvider() {
        super(null, null, null);
    }

    @Override
    public InsertionPosition getPosition(URI fileUri, InsertionTerm term) throws TransformException, InternTransformException {
        return new InsertionPosition(1, 0);
    }

    @Override
    public Optional<Integer> GetTermHeapPosition(Term t) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() {
        return 1;
    }
}
