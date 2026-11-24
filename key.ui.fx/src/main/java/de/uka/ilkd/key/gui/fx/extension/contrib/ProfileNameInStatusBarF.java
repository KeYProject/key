/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Control;
import javafx.scene.control.Label;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;

import org.key_project.util.javafx.FxUtil;

/**
 * Status-line extension showing the profile name of the currently selected proof, FX port of
 * {@code de.uka.ilkd.key.gui.extension.impl.ProfileNameInStatusBar} (Swing
 * ProfileNameInStatusBar.java:17-36). The Swing original registers a {@code KeYSelectionListener}
 * that writes {@code "Profile: " + mediator.getProfile().ident()} into its label
 * (ProfileNameInStatusBar.java:24-31); the FX port reads the profile of the selected proof
 * instead ({@code mediator.getSelectedProof().getServices().getProfile()},
 * Services.getProfile — the FX {@link KeYMediatorF} has no own {@code getProfile()}) and keeps
 * the label null-safe (no proof → {@code "Profile: -"}). Selection events may fire from the
 * prover thread, so the update is marshalled to the FX thread ({@link FxUtil#runLater}).
 */
@KeYGuiExtensionF.Info(experimental = false, name = "Profile Name in Status Line", optional = false,
    description = "Shows the profile name of the current selected proof in the status line.")
public class ProfileNameInStatusBarF
        implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.StartupF {

    private final Label lblProfileName = new Label();

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.0 — Swing ProfileNameInStatusBar.java:24-31: a KeYSelectionListener
        // updates the label on selectedProofChanged; the initial text is set immediately.
        mediator.getSelectionModel().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                update(mediator);
            }
        });
        update(mediator);
    }

    private void update(KeYMediatorF mediator) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> update(mediator));
            return;
        }
        Proof proof = mediator.getSelectedProof();
        Profile profile = proof != null && proof.getServices() != null
                ? proof.getServices().getProfile()
                : null;
        lblProfileName.setText("Profile: " + (profile == null ? "-" : profile.ident()));
    }

    @Override
    public List<Control> getStatusLineControls() {
        // extension: MP9.0 — Swing ProfileNameInStatusBar.java:34-36: singleton label
        return List.of(lblProfileName);
    }
}
