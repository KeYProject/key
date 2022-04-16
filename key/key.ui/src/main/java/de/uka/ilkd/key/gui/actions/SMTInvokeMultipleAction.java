package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.st.SolverType;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.List;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Opens a dialog to choose multiple available SMT solvers to run at the same time.
 *
 * @author alicia
 */
public final class SMTInvokeMultipleAction extends SMTInvokeAction {

    /**
     * Button label.
     */
    private static final String SELECT_ALL = "Select All";
    /**
     * Button label.
     */
    private static final String START = "Start Solvers";
    /**
     * Button label.
     */
    private static final String CANCEL = "Cancel";
    /**
     * Dialog title.
     */
    private static final String TITLE = "Choose Multiple Solvers";
    /**
     * Font key for the title.
     */
    private static final String LABEL_FONT = "Label.font";
    /**
     * Error message if the action is performed while no proof is loaded.
     */
    private static final String NO_PROOF = "No proof loaded.";
    /**
     * Title for the error message warning dialog.
     */
    private static final String OOPS = "Oops...";

    /**
     * The possible solvers/solver collections that can be chosen to run at the same time.
     */
    private final transient Collection<SolverTypeCollection> possibleSolvers;

    /**
     * Create a new action that lets the user choose multiple of the given solver unions
     * to run at the same time.
     *
     * @param solverUnions the runnable solver unions (each consisting of one or more solvers)
     * @param mainWindow the {@link MainWindow} this action belongs to
     */
    public SMTInvokeMultipleAction(Collection<SolverTypeCollection> solverUnions,
                                   MainWindow mainWindow) {
        super(SolverTypeCollection.EMPTY_COLLECTION, mainWindow);
        this.possibleSolvers = solverUnions;
    }

    @Override
    public boolean isEnabled() {
        return possibleSolvers.size() > 1
                && mediator != null
                && mediator.getSelectedProof() != null
                && !mediator.getSelectedProof().closed();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (!mediator.ensureProofLoaded()) {
            mainWindow.popupWarning(NO_PROOF, OOPS);
            return;
        }

        JDialog choiceDialog = new JDialog(mainWindow);
        choiceDialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        choiceDialog.setLocationByPlatform(true);
        JPanel panel = new JPanel(new BorderLayout(5, 20));
        choiceDialog.setContentPane(panel);
        choiceDialog.setTitle(TITLE);
        // available solver unions
        List<UnionCheckBox> choiceOptions = new LinkedList<>();
        JButton start = new JButton(START);
        // create panel containing start- and cancel-button
        JPanel buttonPanel = makeButtonPanel(choiceDialog, choiceOptions, start, e);
        // create panel containing the solver (union) checkboxes
        JPanel choicePanel = makeChoicePanel(choiceOptions, start);
        panel.add(choicePanel, BorderLayout.NORTH);
        panel.add(buttonPanel, BorderLayout.SOUTH);
        choiceDialog.pack();
        // if the dialog is currently smaller than its title, change its width
        int titleWidth = SwingUtilities.computeStringWidth(
                new JLabel().getFontMetrics(UIManager.getDefaults().getFont(LABEL_FONT)),
                choiceDialog.getTitle());
        choiceDialog.setSize(new Dimension(titleWidth + choiceDialog.getWidth(),
                choiceDialog.getHeight()));
        choiceDialog.setEnabled(true);
        choiceDialog.setVisible(true);
    }

    private JPanel makeButtonPanel(JDialog choiceDialog, List<UnionCheckBox> choiceOptions,
                             JButton start, ActionEvent e) {
        start.setEnabled(false);
        JButton cancel = new JButton(CANCEL);
        cancel.addActionListener(actionEvent -> choiceDialog.dispose());
        start.addActionListener(actionEvent -> {
            new SMTInvokeAction(createSolverTypeCollection(choiceOptions), mainWindow)
                    .actionPerformed(e);
            choiceDialog.dispose();
        });
        JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT));
        buttonPanel.add(start);
        buttonPanel.add(cancel);
        return buttonPanel;
    }

    private JPanel makeChoicePanel(Collection<UnionCheckBox> choiceOptions, JButton start) {
        JPanel choicePanel = new JPanel();
        choicePanel.setLayout(new BoxLayout(choicePanel, BoxLayout.Y_AXIS));

        JCheckBox selectAll = new JCheckBox(SELECT_ALL);
        selectAll.setFocusPainted(false);
        // Change behaviour of checkAll to unchecking all if all solvers are checked
        selectAll.setEnabled(true);
        selectAll.setSelected(true);
        selectAll.addActionListener(changeEvent -> {
            boolean isSelected = selectAll.isSelected();
            for (UnionCheckBox checkBox: choiceOptions) {
                checkBox.setSelected(isSelected);
            }
        });

        Box choiceBox = Box.createVerticalBox();
        choiceBox.setAlignmentX(Component.CENTER_ALIGNMENT);
        choicePanel.add(choiceBox);
        choiceBox.add(selectAll);
        choiceBox.add(new JSeparator());

        for (SolverTypeCollection union: possibleSolvers) {
            UnionCheckBox chooseUnion = new UnionCheckBox(union);
            chooseUnion.setFocusPainted(false);
            chooseUnion.addChangeListener(changeEvent -> {
                // Enable start button iff at least one solver is checked
                if (createSolverTypeCollection(choiceOptions).equals(
                        SolverTypeCollection.EMPTY_COLLECTION)) {
                    start.setEnabled(false);
                    if (selectAll.isSelected()) {
                        selectAll.setSelected(false);
                    }
                    return;
                }
                start.setEnabled(true);
                long count = choiceOptions.stream().filter(AbstractButton::isSelected).count();
                if (count == choiceOptions.size() && !selectAll.isSelected()) {
                    selectAll.setSelected(true);
                }
            });
            choiceOptions.add(chooseUnion);
            chooseUnion.setSelected(true);
            choiceBox.add(chooseUnion);
        }
        return choicePanel;
    }

    private SolverTypeCollection createSolverTypeCollection(Collection<UnionCheckBox> checkBoxes) {
        Set<SolverType> types = new HashSet<>();
        StringBuilder builder = new StringBuilder();
        for (UnionCheckBox box: checkBoxes.stream().filter(AbstractButton::isSelected)
                .collect(Collectors.toList())) {
            types.addAll(box.getUnion().getTypes());
        }
        if (types.isEmpty()) {
            return SolverTypeCollection.EMPTY_COLLECTION;
        }
        for (SolverType type: types) {
            builder.append(type.getName() + ", ");
        }
        builder.delete(builder.length() - 2, builder.length());
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
        return this.possibleSolvers.equals(((SMTInvokeMultipleAction) obj).possibleSolvers);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(possibleSolvers);
    }

    /**
     * A checkbox linked to a SolverTypeCollection.
     */
    private final class UnionCheckBox extends JCheckBox {

        /**
         * The solver union associated with the checkbox at hand.
         */
        private final transient SolverTypeCollection union;

        private UnionCheckBox(SolverTypeCollection union) {
            super(union.name());
            this.union = union;
        }

        private SolverTypeCollection getUnion() {
            return union;
        }

    }

}
