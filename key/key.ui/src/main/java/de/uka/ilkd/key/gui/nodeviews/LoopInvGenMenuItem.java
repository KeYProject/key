package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.loopinvgen.LIGNew;
import de.uka.ilkd.key.loopinvgen.LoopInvariantGenerationResult;
import de.uka.ilkd.key.pp.PosInSequent;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Set;

import static de.uka.ilkd.key.loopinvgen.analyzer.WhileStatementAnalyzer.findPossibleIndexes;
import static de.uka.ilkd.key.loopinvgen.analyzer.WhileStatementAnalyzer.isWhileStatement;

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
                Set<ProgramVariable> possibleIndexes = findPossibleIndexes(posInSequent, mediator.getServices());
                ProgramVariable index = possibleIndexes.iterator().next();
                if (possibleIndexes.size() > 1) {
                    index = selectIndex(possibleIndexes);
                }

                final LIGNew loopInvGenerator = new LIGNew(mediator.getSelectedGoal().sequent(), mediator.getServices(), index);
                LoopInvariantGenerationResult result = loopInvGenerator.generate();
                showResultInWindow(result.toString());
            }
        });
        setEnabled(isWhileStatement(posInSequent));
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
