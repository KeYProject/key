/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Proof;

@KeYGuiExtension.Info(experimental = false, name = "Profile Name in Status Line", optional = false,
    description = "Shows the profile name of the current selected proof in the status line.")
public class ProfileNameInStatusBar
        implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup {
    private final JLabel lblProfileName = new JLabel();

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                lblProfileName.setText("Profile: " + mediator.getProfile().ident());
            }
        });
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(lblProfileName);
    }
}
