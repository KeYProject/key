package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.loopinvgen.LIGNew;
import de.uka.ilkd.key.loopinvgen.LoopInvariantGenerationResult;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Set;

public class LoopInvGenMenuItem extends JMenuItem {
    private final KeYMediator mediator;
    private final PosInSequent posInSequent;

    public LoopInvGenMenuItem(KeYMediator mediator, PosInSequent posInSequent) {
        super("LoopInvGeneration");
        this.mediator = mediator;
        this.posInSequent = posInSequent;
        addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (isClickable()) {
                    Services services = mediator.getServices();
                    PosInOccurrence pos = posInSequent.getPosInOccurrence();

                    //System.out.println(ProofSaver.printAnything(pos.subTerm(), services));
                    //System.out.println(pos.isInAntec() + ": " + pos.posInTerm());

                    Term loopFormula = pos.subTerm();
                    Term loopFormulaWithoutUpdates = TermBuilder.goBelowUpdates(loopFormula);
                    JavaProgramElement statement = loopFormulaWithoutUpdates.javaBlock().program();
                    StatementBlock statementBlock = (StatementBlock) statement;

                    While whileStatement = (While) statementBlock.getStatementAt(0);
                    ProgramVariableCollector pvc = new ProgramVariableCollector(whileStatement.getGuardExpression(), services);

                    //find index in loop
                    ImmutableSet<ProgramVariable> variablesInGuard = MiscTools.getLocalIns(whileStatement.getGuardExpression(), services);
                    ImmutableSet<ProgramVariable> variablesInWhile = MiscTools.getLocalOuts(whileStatement, services);
                    Set<ProgramVariable> counters = variablesInGuard.toSet();
                    counters.retainAll(variablesInWhile.toSet());
                    ProgramVariable index = counters.iterator().next();
                    if (counters.size() > 1) {
                        index = selectIndex(counters);
                    }

                    pvc.start();
                    pvc.result();

                    final LIGNew loopInvGenerator = new LIGNew(mediator.getSelectedGoal().sequent(), mediator.getServices(), index);
                    LoopInvariantGenerationResult result = loopInvGenerator.generate();
                    showResultInWindow(result.toString());
                }
            }
        });
    }

    public boolean isClickable() {
        Services services = mediator.getServices();
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

    private static void showResultInWindow(String text) {
        JFrame frame = new JFrame("Loop Invariant Generation Result");
        JTextArea textArea = new JTextArea(20, 40);
        textArea.setText(text);
        textArea.setEditable(false);
        JScrollPane scrollPane = new JScrollPane(textArea);

        frame.add(scrollPane);
        frame.pack();
        frame.setLocationRelativeTo(null);
        frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        frame.setVisible(true);
    }

    public static ProgramVariable selectIndex(Set<ProgramVariable> indexes) {

        JDialog dialog = new JDialog((Frame) null, "Select the loop's index", true);
        dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
        dialog.setLayout(new BorderLayout());

        dialog.setPreferredSize(new Dimension(300, 100));

        JComboBox<ProgramVariable> comboBox = new JComboBox<>(indexes.toArray(new ProgramVariable[0]));
        dialog.add(comboBox, BorderLayout.CENTER);

        JButton okButton = new JButton("OK");

        final ProgramVariable[] selectedIndex = new ProgramVariable[1];

        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                selectedIndex[0] = (ProgramVariable) comboBox.getSelectedItem();
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
