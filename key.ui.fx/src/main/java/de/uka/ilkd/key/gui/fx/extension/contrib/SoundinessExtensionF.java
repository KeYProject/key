/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.MenuItem;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.soundiness.SoundinessDialogF;
import de.uka.ilkd.key.proof.Proof;

/**
 * Extension that adds soundiness report functionality to the UI, FX port of
 * {@code SoundinessExtension} (Swing {@code gui/extension/impl/SoundinessExtension.java}): adds
 * the context menu item to the proof list (Swing adds a {@code ShowSoundinessAction} to
 * {@code ContextMenuKind.PROOF_LIST} for every proof, SoundinessExtension.java:36-43) and
 * enables soundiness analysis. The Proof menu's "Soundiness Report" item (smalldialogs) reaches
 * the same dialog for the selected proof; this extension covers the right-clicked proof.
 */
@KeYGuiExtensionF.Info(name = "Soundiness Report",
    description = "Provides soundiness analysis for proofs showing assumptions, unsound choices, "
        + "and verification limitations.",
    experimental = false, optional = true, priority = 1000)
public class SoundinessExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.ContextMenuF {

    @Override
    public List<MenuItem> getProofListContextItems(KeYMediatorF mediator, Proof proof) {
        // Swing SoundinessExtension.getContextActions: the ShowSoundinessAction is contributed
        // for proofs only
        MainWindowF window = MainWindowF.getInstance();
        if (window == null) {
            return List.of();
        }
        MenuItem item = new MenuItem("Show Soundiness Report");
        item.setOnAction(
            e -> new SoundinessDialogF(window.getStage(), proof).showCenteredOnOwner());
        return List.of(item);
    }

    @Override
    public List<MenuItem> getSequentContextItems(KeYMediatorF mediator,
            de.uka.ilkd.key.proof.Goal goal, de.uka.ilkd.key.pp.PosInSequent pos) {
        // the soundiness extension serves only the proof-list slot (Swing returns no actions for
        // the other context menu kinds)
        return List.of();
    }
}
