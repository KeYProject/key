package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.JTerm;
import org.key_project.prover.sequent.Sequent;

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
    public Optional<Integer> getTermHeapPosition(Sequent s, JTerm t, InsertionType itype) {
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
