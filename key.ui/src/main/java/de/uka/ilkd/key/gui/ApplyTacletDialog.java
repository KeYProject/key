/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;


import java.awt.*;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.Collection;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/** common superclass of TacletIfSelectionDialog and TacletMatchCompletionDialog */
public abstract class ApplyTacletDialog extends JDialog {


    /**
     *
     */
    private static final long serialVersionUID = -411398660828882035L;
    private static final Logger LOGGER = LoggerFactory.getLogger(ApplyTacletDialog.class);

    // buttons
    protected final JButton cancelButton;
    protected final JButton applyButton;

    protected final KeYMediator mediator;
    protected final boolean checkAfterEachInput = true;

    protected final TacletInstantiationModel[] model;
    private JTextArea statusArea;

    public ApplyTacletDialog(Frame parent, TacletInstantiationModel[] model, KeYMediator mediator) {

        super(parent, "Choose Taclet Instantiation", false);

        this.mediator = mediator;
        this.model = model;

        applyButton = new JButton("Apply");
        cancelButton = new JButton("Cancel");

        GuiUtilities.attachClickOnEscListener(cancelButton);

        mediator.requestModalAccess(this);
        addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosed(WindowEvent e) {
                ApplyTacletDialog.this.closeDlg();
            }

            @Override
            public void windowClosing(WindowEvent e) {
                ApplyTacletDialog.this.closeDlg();
            }
        });


        getRootPane().setDefaultButton(applyButton);
    }

    protected KeYMediator mediator() {
        return mediator;
    }

    private int countLines(String s) {
        int i = 0;
        int p = 0;
        while ((p = s.indexOf('\n', p)) >= 0) {
            i++;
            p++;
        }
        return i + 1;
    }

    protected JPanel createInfoPanel() {
        Collection<IProgramVariable> vars = model[0].programVariables().elements();
        JPanel panel = new JPanel(new GridLayout(1, 1));
        panel.setBorder(new TitledBorder("Sequent program variables"));
        JScrollPane scroll = new JScrollPane();
        JTextArea text;
        if (!vars.isEmpty()) {
            text = new JTextArea(vars.toString(), 2, 40);
        } else {
            text = new JTextArea("none", 1, 40);
        }
        scroll.setViewportView(text);
        text.setEditable(false);
        panel.add(scroll, BorderLayout.CENTER);
        return panel;
    }

    protected JPanel createTacletDisplay() {
        JPanel panel = new JPanel(new BorderLayout());
        panel.setBorder(new TitledBorder("Selected Taclet - " + model[0].taclet().name()));
        LOGGER.debug("TacletApp: {}", model[0].taclet());

        Taclet taclet = model[0].taclet();
        StringBuilder tacletSB = new StringBuilder();

        SequentViewLogicPrinter tp = SequentViewLogicPrinter.purePrinter(68, new NotationInfo(),
            mediator.getServices(), MainWindow.getInstance().getVisibleTermLabels());

        tp.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
            false);
        tacletSB.append(tp.result());

        panel.setAlignmentY(Component.TOP_ALIGNMENT);
        // show taclet
        JScrollPane scroll = new JScrollPane();
        int nolines = countLines(model[0].taclet().toString()) + 1;
        if (nolines > 10) {
            nolines = 11;
        }
        JTextArea text = new JTextArea(tacletSB.toString(), nolines, 68);
        text.setEditable(false);
        scroll.setViewportView(text);
        panel.add(scroll, BorderLayout.CENTER);

        return panel;
    }

    protected abstract void pushAllInputToModel();

    protected abstract int current();

    public boolean checkAfterEachInput() {
        return checkAfterEachInput;
    }

    protected JPanel createStatusPanel() {
        JPanel statusPanel = new JPanel(new BorderLayout());

        statusArea = new JTextArea();
        statusArea.setEditable(false);

        statusPanel
                .add(new JScrollPane(statusArea, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED), BorderLayout.CENTER);
        statusPanel.setBorder(new TitledBorder("Input validation result"));
        setStatus(model[current()].getStatusString());
        return statusPanel;
    }

    protected JPanel createButtonPanel(ActionListener buttonListener) {
        JPanel panel = new JPanel(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();

        cancelButton.addActionListener(buttonListener);
        applyButton.addActionListener(buttonListener);
        c.insets = new Insets(5, 20, 5, 20);
        c.gridx = 0;
        panel.add(cancelButton, c);

        c.gridx = 1;
        panel.add(applyButton, c);
        panel.setAlignmentY(Component.BOTTOM_ALIGNMENT);

        return panel;
    }

    protected void setStatus(String s) {
        if (statusArea != null) {
            statusArea.setText(s);
        }
    }

    protected void closeDlg() {
        mediator.freeModalAccess(this);
    }
}
