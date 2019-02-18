package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.pp.PosInSequent;

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
        this.pos = pos;
        putValue(KeYExtConst.PATH, "Origin");
        setName("Show origin");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        new OriginTermLabelWindow(
                pos.getPosInOccurrence(),
                getMediator().getSelectedNode(),
                getMediator().getServices());
    }
}
