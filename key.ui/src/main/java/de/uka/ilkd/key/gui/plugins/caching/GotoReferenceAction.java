package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

public class GotoReferenceAction extends MainWindowAction implements KeYSelectionListener {

    public GotoReferenceAction(MainWindow mainWindow) {
        super(mainWindow);
        putValue(SMALL_ICON, IconFactory.BACKREFERENCE_ARROW.get(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Go to referenced proof.");
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
        Node node = getMediator().getSelectedNode();
        if (node == null) {
            // no proof loaded
            setEnabled(false);
        } else {
            boolean anyReferences = node.lookup(ClosedBy.class) != null;
            setEnabled(anyReferences);
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Node ref = getMediator().getSelectedNode().lookup(ClosedBy.class).getNode();
        getMediator().getSelectionModel().setSelectedNode(ref);
    }
}
