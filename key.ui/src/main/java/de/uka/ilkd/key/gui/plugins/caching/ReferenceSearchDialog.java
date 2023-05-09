package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Dialog showing launched SMT processes and results.
 */
public class ReferenceSearchDialog extends JDialog {

    private static final long serialVersionUID = 1L;
    private final ReferenceSearchTable table;
    /**
     * Button to apply the results of running the SMT solver.
     * May close some open goals if the solver returned unsat.
     */
    private JButton applyButton;
    /**
     * Button to stop the launched SMT solvers.
     */
    private JButton stopButton;
    /**
     * Scroll pane listing the open goals and the results of running each SMT solver on them.
     */
    private JScrollPane scrollPane;
    private final ReferenceSearchDialogListener listener;

    public ReferenceSearchDialog(Proof proof, ReferenceSearchDialogListener listener) {
        super(MainWindow.getInstance());
        table = new ReferenceSearchTable(proof);
        table.getTableHeader().setReorderingAllowed(false);
        this.setLocationByPlatform(true);
        this.setTitle("Proof Caching");
        this.listener = listener;

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        setModal(true);
        Container contentPane = this.getContentPane();
        contentPane.setLayout(new GridBagLayout());
        Box buttonBox = Box.createHorizontalBox();
        buttonBox.add(Box.createHorizontalGlue());
        buttonBox.add(getStopButton());
        buttonBox.add(Box.createHorizontalStrut(5));
        buttonBox.add(getApplyButton());


        GridBagConstraints constraints = new GridBagConstraints(0, 0, 1, 1, 1.0, 0.0,
            GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 0, 5), 0, 0);

        constraints.gridy++;
        constraints.weighty = 2.0;
        contentPane.add(getScrollPane(), constraints);
        constraints.gridy++;
        constraints.weighty = 1.0;
        constraints.insets.bottom = 5;
        contentPane.add(buttonBox, constraints);

        if (proof.openGoals().stream().anyMatch(g -> g.node().lookup(ClosedBy.class) != null)) {
            getApplyButton().setEnabled(true);
        }

        this.pack();
    }

    private JButton getApplyButton() {
        if (applyButton == null) {
            applyButton = new JButton("Copy");
            applyButton.setToolTipText(
                "Apply the results (i.e. copy steps into current proof)");
            applyButton.setEnabled(false);
            applyButton.addActionListener(e -> {
                try {
                    listener.copyButtonClicked();
                } catch (Exception exception) {
                    // There may be exceptions during rule application that should not be lost.
                    IssueDialog.showExceptionDialog(ReferenceSearchDialog.this, exception);
                }
            });
        }
        return applyButton;
    }

    private JScrollPane getScrollPane() {
        if (scrollPane == null) {
            scrollPane = new JScrollPane(table, ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_ALWAYS);

            Dimension dim = new Dimension(table.getPreferredSize());
            dim.width += (Integer) UIManager.get("ScrollBar.width") + 2;
            dim.height = scrollPane.getPreferredSize().height;
            scrollPane.setPreferredSize(dim);

        }
        return scrollPane;
    }

    private JButton getStopButton() {
        if (stopButton == null) {
            stopButton = new JButton("Close");
            stopButton.addActionListener(e -> {
                listener.discardButtonClicked();
            });
        }
        return stopButton;
    }
}
