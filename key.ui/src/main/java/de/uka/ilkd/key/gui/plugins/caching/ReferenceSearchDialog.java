/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.key_project.util.java.SwingUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog showing reference search information.
 *
 * @author Arne Keller
 */
public class ReferenceSearchDialog extends JDialog {

    private static final long serialVersionUID = 1L;
    private static final Logger LOGGER = LoggerFactory.getLogger(ReferenceSearchDialog.class);

    /**
     * The table of reference search results.
     */
    private final ReferenceSearchTable table;
    /**
     * Button to copy the relevant proof steps.
     */
    private JButton applyButton;
    /**
     * Button to close the dialog.
     */
    private JButton closeDialog;
    /**
     * Scroll pane listing the open goals and the results of running each SMT solver on them.
     */
    private JScrollPane scrollPane;
    /**
     * Overall progress of the search / copy.
     */
    private final JProgressBar progressBar;
    /**
     * Listener used to react to user inputs.
     */
    private final ReferenceSearchDialogListener listener;

    /**
     * Construct a new dialog. Use {@link #setVisible(boolean)} afterwards to show it.
     *
     * @param proof the proof
     * @param listener control listener
     */
    public ReferenceSearchDialog(Proof proof, ReferenceSearchDialogListener listener) {
        super(MainWindow.getInstance());
        table = new ReferenceSearchTable(proof, MainWindow.getInstance().getMediator());
        table.getTableHeader().setReorderingAllowed(false);
        this.setLocationByPlatform(true);
        this.setTitle("Proof Caching");
        this.listener = listener;

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        setModal(true);

        Container contentPane = this.getContentPane();
        contentPane.setLayout(new GridBagLayout());

        progressBar = new JProgressBar();
        progressBar.setString("Finished.");
        progressBar.setStringPainted(true);
        progressBar.setMaximum(1);
        progressBar.setValue(1);
        Box buttonBox = Box.createHorizontalBox();
        buttonBox.add(Box.createHorizontalGlue());
        buttonBox.add(getCloseDialog());
        buttonBox.add(Box.createHorizontalStrut(5));
        buttonBox.add(getApplyButton());


        GridBagConstraints constraints = new GridBagConstraints(0, 0, 1, 1, 1.0, 0.0,
            GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 0, 5), 0, 0);

        contentPane.add(progressBar, constraints);
        constraints.gridy++;
        constraints.weighty = 2.0;
        contentPane.add(getScrollPane(), constraints);
        constraints.gridy++;
        constraints.weighty = 1.0;
        constraints.insets.bottom = 5;
        contentPane.add(buttonBox, constraints);

        if (proof.closedGoals().stream().anyMatch(g -> g.node().lookup(ClosedBy.class) != null)) {
            getApplyButton().setEnabled(true);
        }

        this.pack();
    }

    private JButton getApplyButton() {
        if (applyButton == null) {
            applyButton = new JButton("Apply");
            applyButton.setToolTipText(
                "Apply the results (i.e. copy steps into current proof)");
            applyButton.setEnabled(false);
            applyButton.addActionListener(e -> {
                try {
                    applyButton.setEnabled(false);
                    closeDialog.setEnabled(false);
                    listener.copyButtonClicked(this);
                } catch (Exception exception) {
                    // There may be exceptions during rule application that should not be lost.
                    LOGGER.error("", exception);
                    IssueDialog.showExceptionDialog(ReferenceSearchDialog.this, exception);
                }
            });
        }
        return applyButton;
    }

    public void apply() {
        getApplyButton().doClick();
    }

    private JScrollPane getScrollPane() {
        if (scrollPane == null) {
            scrollPane = SwingUtil.createScrollPane(table);
        }
        return scrollPane;
    }

    private JButton getCloseDialog() {
        if (closeDialog == null) {
            closeDialog = new JButton("Close");
            closeDialog.addActionListener(e -> listener.closeButtonClicked(this));
        }
        return closeDialog;
    }

    /**
     * Set the maximum value of the progress bar.
     * Also resets progress to zero.
     *
     * @param total total value
     */
    public void setMaximum(int total) {
        progressBar.setMaximum(total);
        progressBar.setValue(0);
        progressBar.setString("Working...");
    }

    /**
     * Increment progress by one.
     *
     * @return whether progress is full
     */
    public boolean incrementProgress() {
        progressBar.setValue(progressBar.getValue() + 1);
        if (progressBar.getValue() == progressBar.getMaximum()) {
            progressBar.setString("Finished.");
            return true;
        }
        return false;
    }
}
