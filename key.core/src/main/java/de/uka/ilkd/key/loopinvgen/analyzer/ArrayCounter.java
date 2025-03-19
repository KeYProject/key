package de.uka.ilkd.key.loopinvgen.analyzer;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;

import java.util.HashSet;
import java.util.Set;

public class ArrayCounter extends JavaASTVisitor {

    private final Set<ProgramVariable> arrays = new HashSet<ProgramVariable>();

    /**
     * create the JavaASTVisitor
     *
     * @param root     the ProgramElement where to begin
     * @param services the Services object
     */
    public ArrayCounter(ProgramElement root, Services services) {
        super(root, services);
    }

    @Override
    protected void doDefaultAction(SourceElement node) {

    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        if (x.getKeYJavaType().getSort() instanceof ArraySort) {
            arrays.add(x);
        }
    }

    public int getNumberOfArrays() {
        return arrays.size();
    }
}
