/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen.analyzer;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import javax.swing.*;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

import org.key_project.logic.Name;

import org.jetbrains.annotations.NotNull;

public class WhileStatementAnalyzer {
    public static boolean isWhileStatement(PosInSequent posInSequent) {
        if (posInSequent == null)
            return false;
        PosInOccurrence pos = posInSequent.getPosInOccurrence();
        if (pos == null)
            return false;

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
                return (LoopStatement) TermBuilder.goBelowUpdates(f).javaBlock().program()
                        .getFirstElement();
            }
        }
        return null;
    }

    private static boolean isWhileFormula(Term f) {
        Term form = TermBuilder.goBelowUpdates(f);
        return form.op() instanceof Modality
                && form.javaBlock().program().getFirstElement() instanceof While;
    }

    public static List<Set<LocationVariable>> findPossibleIndexes(PosInSequent posInSequent,
            Services services) {
        While whileStatement = posInSequentToWhile(posInSequent);

        IndexCollector indexCollector = new IndexCollector(whileStatement, services);
        indexCollector.start();
        return indexCollector.getIndexes();
    }

    private static While posInSequentToWhile(PosInSequent posInSequent) {
        PosInOccurrence pos = posInSequent.getPosInOccurrence();

        Term loopFormula = pos.subTerm();
        Term loopFormulaWithoutUpdates = TermBuilder.goBelowUpdates(loopFormula);
        JavaProgramElement statement = loopFormulaWithoutUpdates.javaBlock().program();
        StatementBlock statementBlock = (StatementBlock) statement;

        return (While) statementBlock.getStatementAt(0);
    }

    public static int findNumberOfArrays(PosInSequent posInSequent, Services services) {
        While whileStatement = posInSequentToWhile(posInSequent);
        ArrayCounter arrayCounter = new ArrayCounter(whileStatement, services);
        arrayCounter.start();
        return arrayCounter.getNumberOfArrays();
    }

    public static Term determineInitialIndex(Sequent sequent, Term index, Services services) {

        JFunction init = getNewInitPredicate(services);

        var tb = services.getTermBuilder();
        var initFormula = tb.func(
            init, index);
        SequentFormula progForIndex = determineLoopFormula(sequent);
        var updateAndFormula = TermBuilder.goBelowUpdates2(progForIndex.formula());
        var initFormulaWithUpdates = tb.apply(tb.seqUpdate(updateAndFormula.first), initFormula);
        Sequent changedSequent = sequent.changeFormula(new SequentFormula(initFormulaWithUpdates),
            new PosInOccurrence(progForIndex, PosInTerm.getTopLevel(), false)).sequent();
        ProofStarter proofStarter = new ProofStarter(false);

        ProofEnvironment env =
            SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
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

    private static @NotNull JFunction getNewInitPredicate(Services services) {
        boolean unusedFound = false;
        String nameInit = "init";
        for (int i = 0; !unusedFound; i++) {
            try {
                JFunction init = new JFunction(new Name(nameInit), JavaDLTheory.FORMULA,
                    services.getTypeConverter().getIntegerLDT().targetSort());
                services.getNamespaces().functions().addSafely(init);
                unusedFound = true;
            } catch (RuntimeException e) {
                nameInit += i;
            }
        }
        return new JFunction(new Name(nameInit), JavaDLTheory.FORMULA,
            services.getTypeConverter().getIntegerLDT().targetSort());
    }

    private static Term determineLowerBound(Sequent sequent, JFunction init) {
        for (SequentFormula sF : sequent) {
            Term form = sF.formula();
            if (form.op() == init) {
                return form.sub(0);
            }
        }
        return null;
    }

    public static List<LocationVariable> findIndexes(List<Set<LocationVariable>> possibleIndexes) {
        List<LocationVariable> result = new LinkedList<>();
        for (int i = 0; i < possibleIndexes.size(); i++) {
            if (possibleIndexes.get(i).isEmpty()) {
                result.add(null);
            } else if (possibleIndexes.get(i).size() == 1) {
                result.add(possibleIndexes.get(i).iterator().next());
            } else {
                String loopDefinition = "";
                if (possibleIndexes.size() > 1) {
                    if (i == possibleIndexes.size() - 1) {
                        loopDefinition = "innermost ";
                    } else {
                        loopDefinition = (i + 1) + "-outermost ";
                    }
                }
                result.add(selectIndex(possibleIndexes.get(i), loopDefinition));
            }
        }
        return result;
    }

    private static LocationVariable selectIndex(Set<LocationVariable> indexes,
            String loopDefinition) {

        JDialog dialog =
            new JDialog((Frame) null, "Select the " + loopDefinition + "loop's index", true);
        dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
        dialog.setLayout(new BorderLayout());

        dialog.setPreferredSize(new Dimension(300, 100));

        JComboBox<ProgramVariable> comboBox =
            new JComboBox<>(indexes.toArray(new LocationVariable[0]));
        dialog.add(comboBox, BorderLayout.CENTER);

        JButton okButton = new JButton("OK");

        final LocationVariable[] selectedIndex = new LocationVariable[1];

        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                selectedIndex[0] = (LocationVariable) comboBox.getSelectedItem();
                dialog.dispose();
            }
        });

        JPanel buttonPanel = new JPanel();
        buttonPanel.add(okButton);
        dialog.add(buttonPanel, BorderLayout.SOUTH);

        dialog.pack();
        dialog.setLocationRelativeTo(null);
        dialog.setVisible(true);

        return selectedIndex[0];
    }
}
