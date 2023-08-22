/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofdiff;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Enumeration;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class ProofDifferenceView extends JPanel {
    public static final String PROPERTY_LEFT_NODE = "left";
    public static final String PROPERTY_RIGHT_NODE = "right";
    private final SequentDifferencesView contentPanel;

    private final Services services;
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);
    private final DefaultComboBoxModel<Proof> listModelLeft = new DefaultComboBoxModel<>();
    private final DefaultComboBoxModel<Proof> listModelRight = new DefaultComboBoxModel<>();
    private final KeYMediator mediator;
    private Node left, right;

    private final JComboBox<Proof> listLeftProof = new JComboBox<>();
    private final JComboBox<Proof> listRightProof = new JComboBox<>();

    public ProofDifferenceView(@Nonnull Node left, @Nonnull Node right, KeYMediator mediator,
            VisibleTermLabels termLabels) {
        this.mediator = mediator;
        this.services = mediator.getServices();

        contentPanel = new SequentDifferencesView(left.proof().getServices(),
            right.proof().getServices(), termLabels);
        contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.Y_AXIS));
        setLayout(new BorderLayout());
        add(new JScrollPane(contentPanel));

        JPanel pNorth = new JPanel(new FlowLayout(FlowLayout.CENTER));
        Box pNorthLeft = new Box(BoxLayout.Y_AXIS);
        Box pNorthRight = new Box(BoxLayout.Y_AXIS);
        JLabel lblLeftNode = new JLabel("Left Node:");
        JLabel lblRightNode = new JLabel("Right Node:");
        JTextField txtLeftNode = new JTextField();
        JTextField txtRightNode = new JTextField();
        pNorthLeft.add(lblLeftNode);
        pNorthLeft.add(listLeftProof);
        pNorthLeft.add(txtLeftNode);
        pNorthRight.add(lblRightNode);
        pNorthRight.add(listRightProof);
        pNorthRight.add(txtRightNode);

        txtRightNode.addActionListener(e -> setRight(findNode(listRightProof, txtRightNode)));
        txtLeftNode.addActionListener(e -> setLeft(findNode(listLeftProof, txtLeftNode)));
        listRightProof.addActionListener(e -> setRight(findNode(listRightProof, txtRightNode)));
        listLeftProof.addActionListener(e -> setLeft(findNode(listLeftProof, txtLeftNode)));

        pNorth.add(pNorthLeft);
        pNorth.add(new JSeparator(JSeparator.VERTICAL));
        pNorth.add(pNorthRight);

        txtLeftNode.setText(String.valueOf(left.serialNr()));
        txtRightNode.setText(String.valueOf(right.serialNr()));

        listLeftProof.setModel(listModelLeft);
        listRightProof.setModel(listModelRight);
        mediator.getCurrentlyOpenedProofs().addListDataListener(new ListDataListener() {
            @Override
            public void intervalAdded(ListDataEvent e) {
                transferProofs();
            }

            @Override
            public void intervalRemoved(ListDataEvent e) {
                transferProofs();
            }

            @Override
            public void contentsChanged(ListDataEvent e) {
                transferProofs();
            }
        });
        transferProofs();
        ListCellRenderer<? super Proof> renderer = new DefaultListCellRenderer() {
            @Override
            public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                return super.getListCellRendererComponent(list, ((Proof) value).name(), index,
                    isSelected, cellHasFocus);
            }
        };
        listRightProof.setRenderer(renderer);
        listLeftProof.setRenderer(renderer);
        listRightProof.setSelectedItem(right.proof());
        listLeftProof.setSelectedItem(left.proof());

        addPropertyChangeListener(evt -> {
            if (this.left != null && this.right != null) {
                contentPanel.setLeft(left.sequent());
                contentPanel.setRight(right.sequent());
            }
        });

        add(pNorth, BorderLayout.NORTH);
        JPanel pSouth = new JPanel();
        JCheckBox chkBox = new JCheckBox(contentPanel.getActionHideCommonFormulas());
        pSouth.add(chkBox);
        add(pSouth, BorderLayout.SOUTH);

        this.setLeft(left);
        this.setRight(right);
    }

    public DefaultMultipleCDockable asDockable() {
        var dockable = new DefaultMultipleCDockable(NullMultipleCDockableFactory.NULL,
            "Proof Differences", this);
        dockable.setCloseable(true);
        dockable.setRemoveOnClose(true);
        dockable.addAction(HelpFacade.createHelpButton("user/NodeDiff/"));
        dockable.setLayout(new BorderLayout());
        addPropertyChangeListener(evt -> {
            if (this.left != null && this.right != null) {
                dockable.setTitleText(
                    "Difference between: " + left.serialNr() + " and " + right.serialNr());
            }
        });
        return dockable;
    }

    private Node findNode(JComboBox<Proof> box, JTextField text) {
        try {
            int serialNr = Integer.parseInt(text.getText());
            Proof proof = (Proof) box.getSelectedItem();
            if (proof == null)
                return null;
            return proof.findAny(n -> n.serialNr() == serialNr);
        } catch (NumberFormatException ignored) {

        }
        return null;
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(listener);
    }

    public Services getServices() {
        return services;
    }

    @Nonnull
    public Node getLeft() {
        return left;
    }

    public void setLeft(@Nullable Node left) {
        if (left == null)
            return;
        Node oldLeft = this.left;
        this.left = left;
        propertyChangeSupport.firePropertyChange(PROPERTY_LEFT_NODE, oldLeft, left);
    }

    @Nonnull
    public Node getRight() {
        return right;
    }

    public void setRight(@Nullable Node right) {
        if (right == null)
            return;
        Node old = this.right;
        this.right = right;
        propertyChangeSupport.firePropertyChange(PROPERTY_RIGHT_NODE, old, right);
    }

    private void transferProofs() {
        listModelLeft.removeAllElements();
        listModelRight.removeAllElements();
        Enumeration<Proof> iter = mediator.getCurrentlyOpenedProofs().elements();
        while (iter.hasMoreElements()) {
            Proof proof = iter.nextElement();
            listModelLeft.addElement(proof);
            listModelRight.addElement(proof);
        }
    }

    static class MyPanel extends JPanel implements Scrollable {
        private static final long serialVersionUID = -3046025680639399997L;

        MyPanel(LayoutManager layout) {
            super(layout);
        }

        public Dimension getPreferredScrollableViewportSize() {
            return getPreferredSize();
        }

        public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation,
                int direction) {
            return 0;
        }

        public boolean getScrollableTracksViewportHeight() {
            return false;
        }

        public boolean getScrollableTracksViewportWidth() {
            return true;
        }

        public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation,
                int direction) {
            return 0;
        }
    }

    public static class OpenDifferenceWithParent extends MainWindowAction {
        private Node left;

        public OpenDifferenceWithParent(MainWindow mainWindow, Node node) {
            super(mainWindow);
            setName("Diff with parent");
            setEnabled(node.parent() != null);
            this.left = node;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofDifferenceView pdv =
                new ProofDifferenceView(left, left.parent(), mainWindow.getMediator(),
                    mainWindow.getVisibleTermLabels());
            var dockable = pdv.asDockable();
            mainWindow.getDockControl().addDockable(dockable);
            dockable.setLocation(CLocation.base());
            dockable.setVisible(true);
        }
    }
}
