package de.uka.ilkd.key.proof.reference;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;

/**
 * Toolbar action to copy over all referenced proof steps.
 *
 * @author Arne Keller
 */
public class CopyStepsAction extends MainWindowAction implements KeYSelectionListener {
    public CopyStepsAction(MainWindow mainWindow) {
        super(mainWindow);
        putValue(SMALL_ICON, IconFactory.BACKREFERENCE.get(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Copy all referenced proof steps.");
        initListeners();
    }

    /**
     * Registers the action at some listeners to update its status in a correct fashion.
     */
    public void initListeners() {
        getMediator().addKeYSelectionListener(this);

        this.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        Proof proof = getMediator().getSelectedProof();
        if (proof == null) {
            // no proof loaded
            setEnabled(false);
        } else {
            boolean anyReferences =
                proof.openGoals().stream().anyMatch(g -> g.node().lookup(ClosedBy.class) != null);
            setEnabled(anyReferences);
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().getSelectedProof().copyCachedGoals(null);
    }
}
