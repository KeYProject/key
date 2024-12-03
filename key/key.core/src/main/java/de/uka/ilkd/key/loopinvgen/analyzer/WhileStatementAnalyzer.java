package de.uka.ilkd.key.loopinvgen.analyzer;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

import java.util.List;
import java.util.Set;

public class WhileStatementAnalyzer {
    public static boolean isWhileStatement(PosInSequent posInSequent) {
        if (posInSequent == null) return false;
        PosInOccurrence pos = posInSequent.getPosInOccurrence();
        if (pos == null) return false;

        Term loopFormula = pos.subTerm();
        if (loopFormula == null) return false;

        Term loopFormulaWithoutUpdates = TermBuilder.goBelowUpdates(loopFormula);
        if (loopFormulaWithoutUpdates == null) return false;

        JavaProgramElement statement = null;
        if (loopFormulaWithoutUpdates.javaBlock().isEmpty()) return false;

        statement = loopFormulaWithoutUpdates.javaBlock().program();
        if (!(statement instanceof StatementBlock)) return false;

        StatementBlock statementBlock = (StatementBlock) statement;
        if (!(statementBlock.getStatementAt(0) instanceof While)) return false;

        return true;
    }

    public static List<Set<ProgramVariable>> findPossibleIndexes(PosInSequent posInSequent, Services services) {
        PosInOccurrence pos = posInSequent.getPosInOccurrence();

        Term loopFormula = pos.subTerm();
        Term loopFormulaWithoutUpdates = TermBuilder.goBelowUpdates(loopFormula);
        JavaProgramElement statement = loopFormulaWithoutUpdates.javaBlock().program();
        StatementBlock statementBlock = (StatementBlock) statement;

        While whileStatement = (While) statementBlock.getStatementAt(0);

        IndexCollector indexCollector = new IndexCollector(whileStatement, services);
        indexCollector.start();
        return indexCollector.getIndexes();
    }

    public static Set<ProgramVariable> findPossibleIndexes2(PosInSequent posInSequent, Services services) {
        PosInOccurrence pos = posInSequent.getPosInOccurrence();

        Term loopFormula = pos.subTerm();
        Term loopFormulaWithoutUpdates = TermBuilder.goBelowUpdates(loopFormula);
        JavaProgramElement statement = loopFormulaWithoutUpdates.javaBlock().program();
        StatementBlock statementBlock = (StatementBlock) statement;

        While whileStatement = (While) statementBlock.getStatementAt(0);

        //find index in loop
        ImmutableSet<ProgramVariable> variablesInGuard = MiscTools.getLocalIns(whileStatement.getGuardExpression(), services);
        ImmutableSet<ProgramVariable> variablesInWhile = MiscTools.getLocalOuts(whileStatement, services);
        Set<ProgramVariable> counters = variablesInGuard.toSet();
        counters.retainAll(variablesInWhile.toSet());

        return counters;
    }
}
