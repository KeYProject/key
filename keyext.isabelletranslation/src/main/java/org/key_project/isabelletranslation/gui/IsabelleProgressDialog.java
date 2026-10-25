/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.gui;

import java.awt.*;
import javax.swing.*;
import javax.swing.event.TableModelEvent;
import javax.swing.plaf.basic.BasicProgressBarUI;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableColumn;
import javax.swing.table.TableColumnModel;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;

import org.key_project.isabelletranslation.gui.IsabelleProgressModel.ProcessColumn.ProcessData;
import org.key_project.util.java.SwingUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog showing launched Isabelle processes and results.
 * <p>
 * Adapted version of {@link de.uka.ilkd.key.gui.smt.ProgressDialog} used for SMT.
 */
@NullMarked
public class IsabelleProgressDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProgressDialog.class);

    /**
     * Contains the progress of all solvers.
     */
    private final ProgressTable table;
    /**
     * Button to apply the results of running the Isabelle solvers.
     * May close some open goals if the solvers found proofs.
     */
    private @Nullable JButton applyButton;
    /**
     * Button to stop the launched Isabelle solvers.
     */
    private @Nullable JButton stopButton;
    /**
     * Scroll pane listing the open goals and the results of running each Isabelle solver on them.
     */
    private @Nullable JScrollPane scrollPane;
    /**
     * Overall progress of the Isabelle solvers (# goals processed / total goals).
     */
    private @Nullable JProgressBar progressBar;
    private final IsabelleProgressDialogListener listener;

    /**
     * Current state of the dialog.
     */
    public enum Modus {
        /**
         * Isabelle solvers are running and may be stopped by the user.
         */
        SOLVERS_RUNNING,
        /**
         * Isabelle solvers are done (or terminated). Results may be applied by the user.
         */
        SOLVERS_DONE
    }

    /**
     * Current state of the dialog.
     */
    private Modus modus = Modus.SOLVERS_RUNNING;

    /**
     * Listener interface to interact with this dialog. Used for functionality of stop, apply and
     * discard buttons.
     */
    public interface IsabelleProgressDialogListener extends ProgressTable.ProgressTableListener {
        void applyButtonClicked();

        void stopButtonClicked();

        void discardButtonClicked();
    }

    /**
     * Creates a new progress dialog.
     *
     * @param model progress model that is displayed in dialog
     * @param listener listener to be used
     * @param resolution resolution to be used for progress bars of each solver
     * @param progressBarMax the total number of goals
     * @param titles titles of the solver types
     */
    /**
     * The dialog-widget calls below operate on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since the widgets are created by
     * the lazy getters before first use and no subclass state is involved, suppressed with a
     * scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public IsabelleProgressDialog(IsabelleProgressModel model,
            IsabelleProgressDialogListener listener,
            boolean counterexample, int resolution, int progressBarMax,
            String... titles) {
        super(MainWindow.getInstance());
        table = new ProgressTable(resolution, listener);
        table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        table.getTableHeader().setReorderingAllowed(false);
        table.setModel(model, titles);
        this.listener = listener;
        this.setTitle("Isabelle Interface");

        getProgressBar().setMaximum(progressBarMax);

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        setModal(true);
        Container contentPane = this.getContentPane();
        contentPane.setLayout(new GridBagLayout());
        Box buttonBox = Box.createHorizontalBox();
        buttonBox.add(Box.createHorizontalGlue());
        buttonBox.add(getStopButton());
        buttonBox.add(Box.createHorizontalStrut(5));
        if (!counterexample) {
            buttonBox.add(Box.createHorizontalStrut(5));
            buttonBox.add(getApplyButton());
            buttonBox.add(Box.createHorizontalStrut(5));
        }


        GridBagConstraints constraints = new GridBagConstraints(0, 0, 1, 1, 1.0, 0.0,
            GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 0, 5), 0, 0);

        contentPane.add(getProgressBar(), constraints);
        constraints.gridy++;
        constraints.weighty = 2.0;
        contentPane.add(getScrollPane(), constraints);
        constraints.gridy += 2;
        constraints.weighty = 0.0;
        constraints.insets.bottom = 5;
        contentPane.add(buttonBox, constraints);
        this.pack();
        // always set the location last, otherwise it is not centered!
        setLocationRelativeTo(MainWindow.getInstance());
    }

    /**
     * Updates the progress bar in the dialog.
     *
     * @param value the new value to set the progress bar to
     */
    public void setProgress(int value) {
        getProgressBar().setValue(value);
    }

    /**
     * Returns the progress bar or creates a new one, if not already created
     *
     * @return the progress bar
     */
    public JProgressBar getProgressBar() {
        if (progressBar == null) {
            progressBar = new JProgressBar();
        }
        return progressBar;
    }

    /**
     * Returns the apply button or creates a new one, if not already created
     *
     * @return the apply button
     */
    private JButton getApplyButton() {
        if (applyButton == null) {
            applyButton = new JButton("Apply");
            applyButton.setToolTipText(
                "Apply the results (i.e. close goals if the Isabelle solver was successful)");
            applyButton.setEnabled(false);
            applyButton.addActionListener(e -> {
                try {
                    listener.applyButtonClicked();
                } catch (Exception exception) {
                    // There may be exceptions during rule application that should not be lost.
                    LOGGER.error("Exception during application of Isabelle results:", exception);
                    IssueDialog.showExceptionDialog(this, exception);
                }
            });
        }
        return applyButton;
    }

    /**
     * Returns the scroll pane or creates a new one, if not already created
     *
     * @return the scroll pane
     */
    private JScrollPane getScrollPane() {
        if (scrollPane == null) {
            scrollPane = SwingUtil.createScrollPane(table);
        }
        return scrollPane;
    }

    /**
     * Returns the stop button or creates a new one, if not already created
     *
     * @return the stop button
     */
    private JButton getStopButton() {
        if (stopButton == null) {
            stopButton = new JButton("Stop");
            stopButton.addActionListener(e -> {
                if (modus.equals(Modus.SOLVERS_DONE)) {
                    listener.discardButtonClicked();
                }
                if (modus.equals(Modus.SOLVERS_RUNNING)) {
                    listener.stopButtonClicked();
                }
            });
        }
        return stopButton;
    }

    /**
     * Switches the modus of the dialog and switches/enables the corresponding buttons.
     * RUNNING -> stop button to interrupt (apply unavailable)
     * DONE -> discard button to discard results (apply available)
     *
     * @param m new modus of dialog
     */
    public void setModus(Modus m) {
        modus = m;
        JButton stop = stopButton;
        if (stop == null) {
            throw new NullPointerException("Stop button was not created.");
        }
        switch (modus) {
            case SOLVERS_DONE -> {
                stop.setText("Discard");
                if (applyButton != null) {
                    applyButton.setEnabled(true);
                }
            }
            case SOLVERS_RUNNING -> {
                stop.setText("Stop");
                if (applyButton != null) {
                    applyButton.setEnabled(false);
                }
            }
        }
    }
}


/**
 * The table displaying the progress of solver instances
 */
@NullMarked
class ProgressTable extends JTable {
    private static final int NUMBER_OF_VISIBLE_ROWS = 8;

    /**
     * Basic listener interface for the table to enable info buttons.
     * currently not working
     */
    public interface ProgressTableListener {
        void infoButtonClicked(int column, int row);
    }

    /**
     * Panel displaying the total progress of all solver instances "x/y instances completed"
     */
    public static class ProgressPanel extends JPanel {
        private @Nullable JProgressBar progressBar;
        private @Nullable JButton infoButton;

        private JProgressBar getProgressBar() {
            if (progressBar == null) {
                JProgressBar bar = new JProgressBar();
                progressBar = bar;
                JButton info = getInfoButton();
                int height = info.getMaximumSize().height;
                bar.setMaximumSize(new Dimension(Integer.MAX_VALUE, height));
                bar.setString("Test");
                bar.setStringPainted(true);
                bar.setFont(getFont());
                return bar;
            }
            return progressBar;
        }

        private JButton getInfoButton() {
            if (infoButton == null) {
                JButton button = new JButton("Info");
                infoButton = button;
                button.setFont(this.getFont());

                Dimension dim = new Dimension();
                button.setMargin(new Insets(0, 0, 0, 0));

                Font font = this.getFont();
                if (font == null) {
                    throw new NullPointerException("No font set on the progress panel.");
                }
                dim.height = this.getFontMetrics(font).getHeight() + 2;
                dim.width = dim.height * 3;

                button.setMinimumSize(dim);
                button.setPreferredSize(dim);
                button.setMaximumSize(dim);
                return button;
            }
            return infoButton;
        }

        /**
         * The {@code this}-based calls below (layout and lazy widget getters) operate on the
         * receiver while it is still under initialization (EISOP initialization check); safe here
         * since the widgets are created by the lazy getters before first use, suppressed with a
         * scoped key.
         */
        @SuppressWarnings({ "nullness:method.invocation.invalid",
            "nullness:argument.type.incompatible" })
        ProgressPanel() {
            this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
            this.add(Box.createVerticalStrut(2));
            Box content = Box.createHorizontalBox();
            content.add(Box.createHorizontalStrut(2));
            content.add(getProgressBar());
            content.add(Box.createHorizontalStrut(2));
            content.add(getInfoButton());
            content.add(Box.createHorizontalStrut(2));
            this.add(content);
            this.add(Box.createVerticalStrut(2));
        }

        /**
         * @param value the new value of the progress bar
         */
        public void setValue(int value) {
            getProgressBar().setValue(value);
        }

        public void setText(@Nullable String text) {
            JProgressBar bar = getProgressBar();
            bar.setString(text == null ? "" : text);
            bar.setStringPainted(text != null && !text.isEmpty());
        }
    }


    private final ProgressPanel progressPanelRenderer = new ProgressPanel();
    private @Nullable ProgressPanel progressPanelEditor;


    private class ProgressCellEditor extends AbstractCellEditor implements TableCellEditor {
        private @Nullable Object currentValue;

        @Override
        public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected,
                int row, int column) {
            currentEditorCell.x = column;
            currentEditorCell.y = row;
            ProcessData data = (ProcessData) value;
            currentValue = value;
            prepareProgressPanel(getProgressPanelEditor(), data);
            return getProgressPanelEditor();
        }


        @Override
        public Object getCellEditorValue() {
            Object value = currentValue;
            if (value == null) {
                throw new NullPointerException("Cell editor value was never initialized.");
            }
            return value;
        }

    }


    private void prepareProgressPanel(ProgressPanel panel, final ProcessData data) {
        JProgressBar progressBar = panel.getProgressBar();
        JButton infoButton = panel.getInfoButton();
        panel.setValue(data.getProgress());
        panel.setText(data.getText());
        infoButton.setEnabled(data.isEditable());
        progressBar.setBackground(data.getBackgroundColor());
        progressBar.setForeground(data.getForegroundColor());
        progressBar.setUI(new BasicProgressBarUI() {


            @Override
            protected Color getSelectionForeground() {
                return data.getSelectedTextColor();
            }

            protected Color getSelectionBackground() {
                return data.getTextColor();
            }
        });

    }


    private final Point currentEditorCell = new Point();


    /**
     * The table-setup calls and the {@code prepareProgressPanel} invocation from the renderer
     * closure operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the {@link ProgressPanel} fields are assigned
     * before any of their methods are invoked, and the font defaults are overridden by the
     * guarded lookup below, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ProgressTable(int resolution, ProgressTableListener listener) {
        TableCellRenderer renderer = (table, value, isSelected, hasFocus, row, column) -> {
            ProcessData data = (ProcessData) value;
            prepareProgressPanel(progressPanelRenderer, data);
            return progressPanelRenderer;
        };
        this.setDefaultRenderer(IsabelleProgressModel.ProcessColumn.class, renderer);
        TableCellEditor editor = new ProgressCellEditor();
        this.setDefaultEditor(IsabelleProgressModel.ProcessColumn.class, editor);
        Font font = this.getFont();
        if (font == null) {
            throw new NullPointerException("No font set on the progress table.");
        }
        init(getProgressPanelEditor(), font, resolution, listener);
        init(progressPanelRenderer, font, resolution, listener);
    }

    private void init(ProgressPanel panel, Font font, int resolution,
            final ProgressTableListener listener) {
        panel.setFont(font);
        panel.getProgressBar().setMaximum(resolution);
        panel.getInfoButton().addActionListener(
            e -> listener.infoButtonClicked(currentEditorCell.x - 1, currentEditorCell.y));
    }


    public void setModel(IsabelleProgressModel model, String... titles) {

        assert titles.length == model.getColumnCount();
        super.setModel(model);
        for (int i = 0; i < titles.length; i++) {
            TableColumn col = getTableHeader().getColumnModel().getColumn(i);

            col.setHeaderValue(titles[i]);
            packColumn(this, i, 5);

        }
        for (int i = 0; i < model.getRowCount(); i++) {
            this.setRowHeight(progressPanelRenderer.getPreferredSize().height + 5);
        }


    }

    @Override
    public Dimension getPreferredScrollableViewportSize() {
        Dimension dim = new Dimension(super.getPreferredScrollableViewportSize());

        dim.height =
            Math.min(NUMBER_OF_VISIBLE_ROWS * (progressPanelRenderer.getPreferredSize().height + 5),
                dim.height);
        return dim;
    }

    public static void packColumn(JTable table, int vColIndex, int margin) {

        TableColumnModel colModel = table.getColumnModel();
        TableColumn col = colModel.getColumn(vColIndex);
        int width;


        TableCellRenderer renderer = col.getHeaderRenderer();
        if (renderer == null) {
            renderer = table.getTableHeader().getDefaultRenderer();
        }
        Component comp =
            renderer.getTableCellRendererComponent(table, col.getHeaderValue(), false, false, 0, 0);
        width = comp.getPreferredSize().width;


        for (int r = 0; r < table.getRowCount(); r++) {
            renderer = table.getCellRenderer(r, vColIndex);
            comp = renderer.getTableCellRendererComponent(table, table.getValueAt(r, vColIndex),
                false, false, r, vColIndex);
            width = Math.max(width, comp.getPreferredSize().width);
        }

        width += 10 * margin;

        col.setPreferredWidth(width);
    }


    private ProgressPanel getProgressPanelEditor() {
        if (progressPanelEditor == null) {
            progressPanelEditor = new ProgressPanel();
        }
        return progressPanelEditor;
    }


    @Override
    public void tableChanged(TableModelEvent e) {
        if (e.getType() == TableModelEvent.UPDATE) {
            this.repaint();

        }
        super.tableChanged(e);
    }

}
