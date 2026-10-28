/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;
import javax.swing.AbstractAction;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Opens a {@link OriginTermLabelVisualizer} for the selected term.
 *
 * @author lanzinger
 */
@NullMarked
public class ShowOriginAction extends MainWindowAction {

    private static final long serialVersionUID = 4557953425770258852L;

    private final PosInSequent pos;

    /**
     * Creates a new {@link ShowOriginAction}.
     *
     * @param pos the position of the term whose origin shall be shown.
     *
     *        <p>
     *        The action names itself, binds its settings listener and accelerator while the
     *        receiver is still under initialization (EISOP initialization check); the listener
     *        only fires once the action is displayed after construction, suppressed with a
     *        scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ShowOriginAction(@Nullable PosInSequent pos) {
        super(MainWindow.getInstance());
        this.pos = pos == null ? PosInSequent.createSequentPos() : pos;

        final TermLabelSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        setName("Show origin");
        setEnabled(settings.getUseOriginLabels());
        settings.addPropertyChangeListener(event -> setEnabled(settings.getUseOriginLabels()));
        setMenuPath("View");
        lookupAcceleratorKey();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        PosInOccurrence pio = pos.getPosInOccurrence();

        // OriginTermLabelVisualizer.TermView can only print sequents or formulas, not terms.
        while (pio != null && !pio.subTerm().sort().equals(JavaDLTheory.FORMULA)) {
            pio = pio.up();
        }

        Node node = getMediator().getSelectedNode();
        Services services = getMediator().getServices();
        if (node == null || services == null) {
            // the action is only usable while a proof with services is loaded
            throw new NullPointerException("No proof node or services available.");
        }
        OriginTermLabelVisualizer vis =
            new OriginTermLabelVisualizer(pio, node, services);

        mainWindow.getSourceViewFrame().addComponent(vis, vis.getLongName(), new AbstractAction() {

            private static final long serialVersionUID = 2410334588447893970L;

            @Override
            public void actionPerformed(ActionEvent e) {
                mainWindow.getSourceViewFrame().removeComponent(vis);
                vis.dispose();
            }
        });
    }
}
