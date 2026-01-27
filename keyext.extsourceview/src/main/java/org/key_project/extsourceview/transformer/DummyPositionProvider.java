package org.key_project.extsourceview.transformer;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;
import org.key_project.extsourceview.Utils;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Optional;

public class DummyPositionProvider extends InsPositionProvider {
    public DummyPositionProvider() {
        super(null, null, null);
    }

    @Override
    public InsertionPosition getPosition(Sequent s, InsertionTerm term) throws TransformException, InternTransformException {
        return new InsertionPosition(1, 1, 0);
    }

    @Override
    public Optional<Integer> GetTermHeapPosition(Sequent s, Term t, InsertionType itype) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() {
        return 1;
    }

    @Override
    public Integer getLoopStartPos() throws TransformException, InternTransformException {
        return 1;
    }

    @Override
    public boolean heapPosAreEqual(int p1, int p2) {
        return p1 == p2;
    }
}
