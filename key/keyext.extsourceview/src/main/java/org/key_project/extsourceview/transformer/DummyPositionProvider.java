package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.Term;

import java.util.Optional;

public class DummyPositionProvider extends InsPositionProvider {
    public DummyPositionProvider() {
        super(null, null, null);
    }

    @Override
    public InsertionPosition getPosition(InsertionTerm term) throws TransformException, InternTransformException {
        return new InsertionPosition(1, 0);
    }

    @Override
    public Optional<Integer> GetTermHeapPosition(Term t, InsertionType itype) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() {
        return 1;
    }
}
