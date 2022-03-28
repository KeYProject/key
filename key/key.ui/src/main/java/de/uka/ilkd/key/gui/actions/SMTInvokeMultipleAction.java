package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.st.SolverType;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;

public final class SMTInvokeMultipleAction extends SMTInvokeAction {

    private final SolverTypeCollection solverUnion;
    private final Collection<SolverTypeCollection> possibleSolvers;
    private static final String SELECT_ALL = "Select All";
    private static final String DESELECT_ALL = "Deselect All";
    private static final String START = "Start Solvers";
    private static final String CANCEL = "Cancel";


    public SMTInvokeMultipleAction(Collection<SolverTypeCollection> solverUnions, MainWindow mainWindow) {
        super(SolverTypeCollection.EMPTY_COLLECTION, mainWindow);
        this.solverUnion = SolverTypeCollection.EMPTY_COLLECTION;
        this.possibleSolvers = solverUnions;
    }

    @Override
    public boolean isEnabled() {
        boolean b = possibleSolvers.size() > 1
                && mediator != null
                && mediator.getSelectedProof() != null
                && !mediator.getSelectedProof().closed();
        return b;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (!mediator.ensureProofLoaded()) {
            mainWindow.popupWarning("No proof loaded.", "Oops...");
            return;
        }

        JDialog choiceDialog = new JDialog(mainWindow);
        choiceDialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        choiceDialog.setLocationByPlatform(true);
        // available solver unions
        List<UnionCheckBox> choiceOptions = new LinkedList<>();

        JButton start = new JButton(START);
        start.setEnabled(false);
        JButton cancel = new JButton(CANCEL);
        cancel.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                choiceDialog.dispose();
            }
        });
        start.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                new SMTInvokeAction(createSolverTypeCollection(choiceOptions), mainWindow).actionPerformed(e);
                choiceDialog.dispose();
            }
        });


        JPanel choicePanel = new JPanel();
        choicePanel.setLayout(new BoxLayout(choicePanel, BoxLayout.Y_AXIS));

        JRadioButton selectAll = new JRadioButton(SELECT_ALL);
        selectAll.setFocusPainted(false);
        // Change behaviour of checkAll to unchecking all if all solvers are checked
        selectAll.setEnabled(true);
        selectAll.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                boolean checkedValue = selectAll.getText().equals(SELECT_ALL);
                for (UnionCheckBox checkBox: choiceOptions) {
                    checkBox.setSelected(checkedValue);
                }
                selectAll.setSelected(false);
            }
        });

        Box choiceBox = Box.createVerticalBox();
        choiceBox.setAlignmentX(Component.CENTER_ALIGNMENT);
        choicePanel.add(choiceBox);
        choiceBox.add(selectAll);
        choiceBox.add(new JSeparator());

        for (SolverTypeCollection union: possibleSolvers){
            UnionCheckBox chooseUnion = new UnionCheckBox(union);
            chooseUnion.setFocusPainted(false);
            chooseUnion.addChangeListener(new ChangeListener() {
                @Override
                public void stateChanged(ChangeEvent e) {
                    // Enable start button iff at least one solver is checked
                    if (createSolverTypeCollection(choiceOptions).equals(SolverTypeCollection.EMPTY_COLLECTION)) {
                        start.setEnabled(false);
                        return;
                    }
                    start.setEnabled(true);
                    selectAll.setText((choiceOptions.stream().filter(u -> u.isSelected())
                            .collect(Collectors.toList()).size() <= choiceOptions.size()/2)
                            ? SELECT_ALL : DESELECT_ALL);
                }
            });
            choiceOptions.add(chooseUnion);
            chooseUnion.setSelected(true);
            choiceBox.add(chooseUnion);
        }

        JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT));
        buttonPanel.add(start);
        buttonPanel.add(cancel);

        JPanel panel = new JPanel(new BorderLayout(5, 20));
        panel.add(choicePanel, BorderLayout.NORTH);
        panel.add(buttonPanel, BorderLayout.SOUTH);
        choiceDialog.setContentPane(panel);
        choiceDialog.setTitle("Choose Multiple Solvers");
        choiceDialog.pack();
        int titleWidth = SwingUtilities.computeStringWidth(
                new JLabel().getFontMetrics(UIManager.getDefaults().getFont("Label.font")),
                choiceDialog.getTitle());
        choiceDialog.setSize(new Dimension(titleWidth + choiceDialog.getWidth(),
                choiceDialog.getHeight()));
        choiceDialog.setEnabled(true);
        choiceDialog.setVisible(true);
    }

    private SolverTypeCollection createSolverTypeCollection(Collection<UnionCheckBox> checkBoxes) {
        Set<SolverType> types = new HashSet<>();
        StringBuilder builder = new StringBuilder();
        for (UnionCheckBox box: checkBoxes.stream().filter(c -> c.isSelected()).collect(Collectors.toList())) {
            types.addAll(box.getUnion().getTypes());
        }
        if (types.size() < 1) {
            return SolverTypeCollection.EMPTY_COLLECTION;
        }
        for (SolverType type: types) {
            builder.append(type.getName() + ", ");
        }
        builder.delete(builder.length()-2, builder.length());
        return new SolverTypeCollection(builder.toString(), types.size(), types);
    }

    @Override
    public String toString() {
        return "Multiple Solvers";
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof SMTInvokeMultipleAction)) {
            return false;
        }
        return this.solverUnion.equals(((SMTInvokeMultipleAction) obj).solverUnion)
                && this.possibleSolvers.equals(((SMTInvokeMultipleAction) obj).possibleSolvers);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(possibleSolvers);
    }

    private class UnionCheckBox extends JCheckBox {

        private SolverTypeCollection union;

        private UnionCheckBox(SolverTypeCollection union) {
            super(union.name());
            this.union = union;
        }

        private SolverTypeCollection getUnion() {
            return union;
        }

    }

}