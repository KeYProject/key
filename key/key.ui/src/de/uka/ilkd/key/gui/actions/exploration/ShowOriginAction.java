package de.uka.ilkd.key.gui.actions.exploration;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.proofExploration.OriginTermLabelWindow;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Opens a {@link OriginTermLabelWindow} for the selected term.
 *
 * @author lanzinger
 */
public class ShowOriginAction extends MainWindowAction {

    private static final long serialVersionUID = -2631175646560838963L;

    private PosInSequent pos;

    public ShowOriginAction(PosInSequent pos) {
        super(MainWindow.getInstance());
        this.pos = pos;
        setName("Show origin");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        new OriginTermLabelWindow(pos.getPosInOccurrence().subTerm(), getMediator().getServices());
    }
}
