package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ProgramMethod;

public class ProgramMethodFinder implements Visitor {

    private boolean foundProgramMethod = false;

    @Override
    public boolean visitSubtree(Term visited) {
        return false;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramMethod) {
            foundProgramMethod = true;
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {

    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {

    }

    public boolean getFoundProgramMethod() {
        return foundProgramMethod;
    }
}
