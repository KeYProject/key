package de.uka.ilkd.key.gui.nodeviews;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.prooftree.ProofTreePopupFactory;
import de.uka.ilkd.key.proof.Node;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class SequentViewDock extends DefaultMultipleCDockable {
    private final SequentView sequentView;
    private final Node node;

    public SequentViewDock(MainWindow mainWindow, Node node) {
        super(NullMultipleCDockableFactory.NULL);
        this.node = node;
        setCloseable(true);
        setRemoveOnClose(true);
        setTitleText("Node: " + node.serialNr());
        sequentView = new InnerNodeView(node, mainWindow);
        JPanel panel = (JPanel) getContentPane();
        panel.setLayout(new BorderLayout());
        panel.add(sequentView);

        addAction(DockingHelper.translateAction(new JumpIntoTreeAction()));
    }

    public static class OpenCurrentNodeAction extends MainWindowAction {
        private final Node node;

        public OpenCurrentNodeAction(MainWindow mainWindow, Node node) {
            super(mainWindow);
            this.node = node;

            setName("Open node in separate buffer");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            SequentViewDock sequentViewDock = new SequentViewDock(mainWindow, node);
            mainWindow.getDockControl().addDockable(sequentViewDock);
            sequentViewDock.setLocation(CLocation.base());
            sequentViewDock.setVisible(true);
        }
    }

    private class JumpIntoTreeAction extends KeyAction {
        JumpIntoTreeAction() {
            setName("Jump into tree");
            putValue(SMALL_ICON, IconFactory.JUMP_INTO_TREE.get());
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (node != null) //TODO Check if also proof needs to be set!
                sequentView.getMainWindow()
                        .getMediator().getSelectionModel()
                        .setSelectedNode(node);
        }
    }
}
