package de.uka.ilkd.key.loopinvgen.analyzer;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.Set;

public class WhileStatementAnalyzer {
    public static boolean isWhileStatement(PosInSequent posInSequent) {
        if (posInSequent == null) return false;
        PosInOccurrence pos = posInSequent.getPosInOccurrence();
        if (pos == null) return false;

        return isWhileFormula(pos.subTerm());
    }

    private static SequentFormula determineLoopFormula(Sequent sequent) {
        for (SequentFormula sF : sequent.succedent()) {
            Term f = sF.formula();
            if (isWhileFormula(f)) {
                return sF;
            }
        }
        return null;
    }

    public static LoopStatement getLoopStatement(Sequent sequent) {
        for (SequentFormula sF : sequent.succedent()) {
            Term f = sF.formula();
            if (isWhileFormula(f)) {
                return (LoopStatement) TermBuilder.goBelowUpdates(f).javaBlock().program().getFirstElement();
            }
        }
        return null;
    }

    private static boolean isWhileFormula(Term f) {
        Term form = TermBuilder.goBelowUpdates(f);
        return form.op() instanceof Modality && form.javaBlock().program().getFirstElement() instanceof While;
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

    public static Term determineInitialIndex(Sequent sequent, Term index, Services services) {

        Function init = getNewInitPredicate(services);

        var tb = services.getTermBuilder();
        var initFormula = tb.func(
                init, index
        );
        SequentFormula progForIndex = determineLoopFormula(sequent);
        var updateAndFormula = TermBuilder.goBelowUpdates2(progForIndex.formula());
        var initFormulaWithUpdates = tb.apply(tb.seqUpdate(updateAndFormula.first), initFormula);
        Sequent changedSequent = sequent.changeFormula(new SequentFormula(initFormulaWithUpdates), new PosInOccurrence(progForIndex, PosInTerm.getTopLevel(), false)).sequent();
        ProofStarter proofStarter = new ProofStarter(false);

        ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        try {
            proofStarter.init(changedSequent, env, "determineInitialIndexValue");
            proofStarter.start();
            assert proofStarter.getProof().openGoals().size() == 1;
            Sequent initSequent = proofStarter.getProof().openGoals().head().sequent();
            var lowerBound = determineLowerBound(initSequent, init);
            System.out.println(lowerBound);
            return lowerBound;
        } catch (ProofInputException e) {
            throw new RuntimeException(e);
        }
    }

    private static @NotNull Function getNewInitPredicate(Services services) {
        boolean unusedFound = false;
        String nameInit = "init";
        for (int i = 0; !unusedFound; i++) {
            try {
                Function init = new Function(new Name(nameInit), Sort.FORMULA, services.getTypeConverter().getIntegerLDT().targetSort());
                services.getNamespaces().functions().addSafely(init);
                unusedFound = true;
            } catch (RuntimeException e) {
                nameInit += i;
            }
        }
        return new Function(new Name(nameInit), Sort.FORMULA, services.getTypeConverter().getIntegerLDT().targetSort());
    }

    private static Term determineLowerBound(Sequent sequent, Function init) {
        for (SequentFormula sF : sequent) {
            Term form = sF.formula();
            if (form.op() == init) {
                return form.sub(0);
            }
        }
        return null;
    }
}
