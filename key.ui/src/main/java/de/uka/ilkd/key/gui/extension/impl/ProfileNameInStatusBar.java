package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import java.util.List;

@KeYGuiExtension.Info(experimental = false, name="Profile Name in Status Line", optional = false,
description = "Shows the profile name of the current selected proof in the status line.")
public class ProfileNameInStatusBar implements KeYGuiExtension,  KeYGuiExtension.StatusLine, KeYGuiExtension.Startup {
    private final JLabel lblProfileName = new JLabel();

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                lblProfileName.setText("Profile: " + mediator.getProfile().name());
            }
        });
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(lblProfileName);
    }
}
