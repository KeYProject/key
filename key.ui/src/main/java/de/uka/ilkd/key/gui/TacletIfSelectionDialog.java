/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * this dialog appears if a rule is selected to be applied and the rule has an if sequent. The
 * dialog offers the possibility to select the wanted match of the if sequent or to enter the
 * if-sequent instantiation manually
 */
public class TacletIfSelectionDialog extends JPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(TacletIfSelectionDialog.class);

    /**
     *
     */
    private static final long serialVersionUID = -7456635942609535650L;
    private JPanel ifPanel = new JPanel();
    private final TacletInstantiationModel model;
    private final TacletMatchCompletionDialog owner;


    /**
     * creates a new dialog
     *
     * @param model the model to be displayed
     */
    public TacletIfSelectionDialog(TacletInstantiationModel model,
            TacletMatchCompletionDialog owner) {

        this.model = model;
        this.owner = owner;
        layoutDialog();
        setVisible(true);
    }

    private void layoutDialog() {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        ifPanel = createIfPanel();
        add(ifPanel);
    }

    /**
     * creates the panel used to select the wanted if instantiation
     */
    private JPanel createIfPanel() {
        JPanel panel = new JPanel();
        panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));
        panel.setBorder(new TitledBorder("Please instantiate the taclet's assumptions:"));

        // If the if-sequent matches to different parts of the sequent
        // the user is given the possibility to choose the right one
        // or to enter an instantiation manually in which case a cut
        // is performed if the manual entry does not match any other
        // part in the sequent. The list of possible the
        // if-instantiations is shown in a combo box model that is
        // created here.
        for (int i = 0; i < model.ifChoiceModelCount(); i++) {
            final JPanel p = new JPanel();
            p.setLayout(new BoxLayout(p, BoxLayout.X_AXIS));
            JLabel label =
                new JLabel(ProofSaver.printAnything(model.ifFma(i), model.proof().getServices())) {
                    /**
                     *
                     */
                    private static final long serialVersionUID = -6925345438533627265L;

                    public java.awt.Dimension getPreferredSize() {
                        return new java.awt.Dimension(100, 10);
                    }
                };
            p.add(label);
            JComboBox<IfFormulaInstantiation> ifChoice = new JComboBox<>(model.ifChoiceModel(i)) {
                /**
                 *
                 */
                private static final long serialVersionUID = -6429999070946158788L;

                public java.awt.Dimension getPreferredSize() {
                    return new java.awt.Dimension(800, (int) super.getPreferredSize().getHeight());
                }
            };
            IfComboRenderer rend = new IfComboRenderer(model.proof().getServices());
            ifChoice.setRenderer(rend);
            ifChoice.addActionListener(e -> {
                JComboBox<?> cb = (JComboBox<?>) e.getSource();
                updateInputField(p, cb);
            });
            p.add(ifChoice);

            updateInputField(p, ifChoice);
            panel.add(p);
        }
        return panel;
    }

    /**
     * the if selection dialog is attached to exact one model
     */
    protected int current() {
        return 0;
    }

    /**
     * requests focus for the the field-th input field and sets the cursor at the given position
     */
    public void requestFocusAt(int field, int col) {
        ifPanel.setVisible(true);
        ifPanel.requestFocus();

        JTextField tf = (JTextField) ((JPanel) ifPanel.getComponent(field)).getComponent(2);
        if (tf == null) {
            LOGGER.debug("None existing field requested");
        }
        if (tf != null && col >= 0 && col < tf.getColumns()) {
            try {
                tf.setCaretPosition(col - 1);
            } catch (IllegalArgumentException iae) {
                LOGGER.debug("Something is wrong with the caret position calculation.", iae);
            } finally {
                tf.requestFocus();
                tf.validate();
            }
        }
        ifPanel.validate();
    }


    private void updateInputField(JPanel parent, JComboBox<?> cb) {
        TacletAssumesModel icm = (TacletAssumesModel) cb.getModel();
        int nr = parent.getComponentCount();
        if (icm.isManualInputSelected() && (nr == 2)) {
            JTextField inp = new JTextField(40);
            inp.addFocusListener(new FocusAdapter() {
                public void focusLost(FocusEvent e) {
                    pushAllInputToModel();
                    owner.setStatus();
                }
            });
            inp.addActionListener(e -> {
                pushAllInputToModel();
                owner.setStatus();
            });

            parent.add(inp);
            inp.setEnabled(true);
        }
        if (!icm.isManualInputSelected() && nr == 3) {
            parent.remove(parent.getComponent(2));
        }
        parent.revalidate();
        pushAllInputToModel();
        owner.setStatus();
    }

    /**
     * transfers input to the model
     */
    protected void pushAllInputToModel() {
        for (int i = 0; i < ifPanel.getComponentCount(); i++) {
            JPanel pan = (JPanel) ifPanel.getComponent(i);
            if ((pan.getComponentCount() == 3)
                    && (((JTextField) pan.getComponent(2)).getText() != null)) {
                model.setManualInput(i, ((JTextField) pan.getComponent(2)).getText());
            } else {
                model.setManualInput(i, "");
            }
        }
    }


    static class IfComboRenderer implements ListCellRenderer<IfFormulaInstantiation> {

        /**
         *
         */
        private static final long serialVersionUID = -7145932915948630147L;
        private final Services services;
        private final DefaultListCellRenderer cellRenderer = new DefaultListCellRenderer();

        public IfComboRenderer(Services services) {
            this.services = services;
        }

        public Component getListCellRendererComponent(JList<? extends IfFormulaInstantiation> list,
                IfFormulaInstantiation value, int index, boolean isSelected, boolean cellHasFocus) {
            cellRenderer.setOpaque(true);
            final String valStr = value.toString(services);
            if (isSelected) {
                list.setToolTipText(valStr);
            }
            return cellRenderer.getListCellRendererComponent(list, valStr, index, isSelected,
                cellHasFocus);
        }
    }
}
