/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;


import java.awt.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import javax.swing.*;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;

/**
 * Common superclass for taclet-instantiation dialogs. It owns the shared
 * {@link TacletInstantiationModel}s and the Apply/Cancel buttons, requests modal access to the
 * mediator and frees it again on close. The concrete layout, input handling and status
 * presentation are left to the subclass
 * ({@link de.uka.ilkd.key.gui.tacletmatch.TacletMatchDialog}).
 */
public abstract class ApplyTacletDialog extends JDialog {

    private static final long serialVersionUID = -411398660828882035L;

    // buttons
    protected final JButton cancelButton;
    protected final JButton applyButton;

    protected final KeYMediator mediator;

    protected final TacletInstantiationModel[] model;

    protected ApplyTacletDialog(Frame parent, TacletInstantiationModel[] model,
            KeYMediator mediator) {

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

    protected abstract void pushAllInputToModel();

    protected abstract int current();

    protected abstract void setStatus(String s);

    protected void closeDlg() {
        mediator.freeModalAccess(this);
    }
}
