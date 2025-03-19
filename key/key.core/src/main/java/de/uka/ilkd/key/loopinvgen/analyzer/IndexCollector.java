package de.uka.ilkd.key.loopinvgen.analyzer;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class IndexCollector extends JavaASTVisitor {

    private final List<Set<ProgramVariable>> indexes = new LinkedList<Set<ProgramVariable>>();

    public IndexCollector(ProgramElement root, Services services) {
        super(root, services);
    }

    @Override
    protected void doDefaultAction(SourceElement node) {

    }

    @Override
    public void performActionOnWhile(While whileStatement) {
        ImmutableSet<ProgramVariable> variablesInGuard = MiscTools.getLocalIns(whileStatement.getGuardExpression(), services);
        ImmutableSet<ProgramVariable> variablesInWhile = MiscTools.getLocalOuts(whileStatement, services);
        Set<ProgramVariable> counters = variablesInGuard.toSet();
        counters.retainAll(variablesInWhile.toSet());
        indexes.add(0, counters);
    }

    public List<Set<ProgramVariable>> getIndexes() {
        return indexes;
    }
}
