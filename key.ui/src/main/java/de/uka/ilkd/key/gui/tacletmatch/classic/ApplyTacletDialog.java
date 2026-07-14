/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch.classic;


import java.awt.*;
import java.awt.event.ActionListener;
import java.util.Collection;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Base for the classic taclet-instantiation dialog.
 *
 * <p>
 * It extends the shared {@link de.uka.ilkd.key.gui.ApplyTacletDialog} so that the sequent view
 * still recognises the dialog (via {@code instanceof ApplyTacletDialog}) and lets a sub-term be
 * dragged from the sequent onto it. On top of that it restores the chrome helper methods (taclet
 * display, program-variable info, status area, button panel) that the shared base shed when the
 * redesigned dialog replaced this one — kept here so the classic dialog stays self-contained.
 */
public abstract class ApplyTacletDialog extends de.uka.ilkd.key.gui.ApplyTacletDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(ApplyTacletDialog.class);

    protected final boolean checkAfterEachInput = true;

    private JTextArea statusArea;

    protected ApplyTacletDialog(Frame parent, TacletInstantiationModel[] model,
            KeYMediator mediator) {
        super(parent, model, mediator);
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

        panel.setAlignmentY(TOP_ALIGNMENT);
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
        panel.setAlignmentY(BOTTOM_ALIGNMENT);

        return panel;
    }

    @Override
    protected void setStatus(String s) {
        if (statusArea != null) {
            statusArea.setText(s);
        }
    }
}
