package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Opens a {@link OriginTermLabelWindow} for the selected term.
 *
 * @author lanzinger
 */
public class ShowOriginAction extends MainWindowAction {

    private static final long serialVersionUID = -2631175646560838963L;

    private PosInSequent pos;

    /**
     * Creates a new {@link ShowOriginAction}.
     *
     * @param pos the position of the term whose origin shall be shown.
     */
    public ShowOriginAction(PosInSequent pos) {
        super(MainWindow.getInstance());
        this.pos = pos == null ? PosInSequent.createSequentPos() : pos;

        final TermLabelSettings settings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        setName("Show origin");
        setEnabled(settings.getUseOriginLabels());
        settings.addSettingsListener(event -> setEnabled(settings.getUseOriginLabels()));
        setMenuPath("View");
        lookupAcceleratorKey();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        PosInOccurrence pio = pos.getPosInOccurrence();

        // TermView can only print sequents or formulas, not terms.
        if (pio != null) {
            while (!pio.subTerm().sort().equals(Sort.FORMULA)) {
                pio = pio.up();
            }
        }

        new OriginTermLabelWindow(
                pio,
                getMediator().getSelectedNode(),
                getMediator().getServices());
    }
}
