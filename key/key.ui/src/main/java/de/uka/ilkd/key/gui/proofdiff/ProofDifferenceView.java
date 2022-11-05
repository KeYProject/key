package de.uka.ilkd.key.gui.proofdiff;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import javax.swing.*;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Enumeration;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class ProofDifferenceView extends DefaultMultipleCDockable {
    public static final String PROPERTY_LEFT_NODE = "left";
    public static final String PROPERTY_RIGHT_NODE = "right";
    private static final String EDITOR_TYPE = "plain/text";
    private final JPanel contentPanel;
    private final KeyAction actionHideCommonFormulas = new HideCommandFormulaAction();
    private final Services services;
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);
    private final DefaultComboBoxModel<Proof> listModelLeft = new DefaultComboBoxModel<>(),
            listModelRight = new DefaultComboBoxModel<>();
    private final KeYMediator mediator;
    private Node left, right;

    private JComboBox<Proof> listLeftProof = new JComboBox<>(), listRightProof = new JComboBox<>();

    public ProofDifferenceView(@Nonnull Node left, @Nonnull Node right, KeYMediator mediator) {
        super(NullMultipleCDockableFactory.NULL);
        this.mediator = mediator;
        this.services = mediator.getServices();
        setCloseable(true);
        setRemoveOnClose(true);
        addAction(HelpFacade.createHelpButton("Using%20Key/NodeDiff"));

        contentPanel = new JPanel();
        contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.Y_AXIS));
        getContentPane().setLayout(new BorderLayout());
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
        // txtLeftNode.setEditable(false);
        // txtRightNode.setEditable(false);
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
            contentPanel.removeAll();
            if (this.left != null && this.right != null) {
                computeDifferences();
                setTitleText("Difference between: " + left.serialNr() + " and " + right.serialNr());
            }
        });

        add(pNorth, BorderLayout.NORTH);
        JPanel pSouth = new JPanel();
        JCheckBox chkBox = new JCheckBox(actionHideCommonFormulas);
        pSouth.add(chkBox);
        add(pSouth, BorderLayout.SOUTH);

        this.setLeft(left);
        this.setRight(right);
    }

    private static void equaliseSize(JComponent txtL, JComponent txtR) {
        Dimension max = new Dimension(Math.max(txtL.getWidth(), txtR.getWidth()),
            Math.max(txtL.getHeight(), txtR.getHeight()));
        txtR.setSize(max);
        txtL.setSize(max);
        txtR.setPreferredSize(max);
        txtL.setPreferredSize(max);
    }

    private Node findNode(JComboBox<Proof> box, JTextField text) {
        try {
            int serialNr = Integer.parseInt(text.getText());
            Proof proof = (Proof) box.getSelectedItem();
            if (proof == null)
                return null;
            return proof.findAny(n -> n.serialNr() == serialNr);
        } catch (NumberFormatException e) {

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

    private void computeDifferences() {
        contentPanel.removeAll();
        ProofDifference pd = ProofDifference.create(services, left, right);
        fill("Antecedent Differences", pd.getAntecPairs());
        /*
         * JSeparator sep = new JSeparator(JSeparator.HORIZONTAL); sep.setForeground(Color.BLACK);
         * sep.setBorder(BorderFactory.createLineBorder(Color.BLACK, 2)); contentPanel.add(sep);
         */
        fill("Succedent Differences", pd.getSuccPairs());

        getContentPane().invalidate();
        getContentPane().revalidate();
        getContentPane().repaint();
        getContentPane().repaint();
        getContentPane().repaint();
    }

    private void fill(String title, List<ProofDifference.Matching> pairs) {
        Box pane = new Box(BoxLayout.Y_AXIS);
        pane.setBorder(BorderFactory.createTitledBorder(title));
        if (!pairs.isEmpty())
            contentPanel.add(pane);
        for (ProofDifference.Matching pair : pairs) {
            // hideCommonFormulas --> distance != 0
            if (!isHideCommonFormulas() || pair.distance > 0) { // skip formulas that have no
                                                                // differences
                JEditorPane txtL = createEditor(pair.left);
                JEditorPane txtR = createEditor(pair.right);
                txtL.setAlignmentX(Component.RIGHT_ALIGNMENT);

                Box boxPair = new Box(BoxLayout.X_AXIS);
                boxPair.add(txtL);
                boxPair.add(new JSeparator(JSeparator.VERTICAL));
                boxPair.add(txtR);
                equaliseSize(txtL, txtR);
                pane.add(boxPair);
                pane.add(new JSeparator(JSeparator.HORIZONTAL));
                // txtL.setRows(3);
                // txtR.setRows(3);
                // contentPanel.add(txtL, cc);
                // contentPanel.add(txtR, cc);
                // hightlightDifferences(txtL, txtR);
            }
        }
    }

    protected JEditorPane createEditor(String content) {
        JEditorPane je = new JEditorPane(EDITOR_TYPE, content != null ? content : "");
        // JTextArea je = new JTextArea(content);
        je.setEditable(false);
        je.setFont(UIManager.getDefaults().getFont(Config.KEY_FONT_SEQUENT_VIEW));
        JPanel textAreaPanel = new JPanel(new BorderLayout());
        textAreaPanel.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
        textAreaPanel.add(je);
        // contentPanel.add(textAreaPanel, new CC().sizeGroup("abc", "abc"));
        return je;
    }

    private void highlightDifferences(JEditorPane txtL, JEditorPane txtR) {
        DefaultHighlighter df1 = new DefaultHighlighter();
        txtL.setHighlighter(df1);
        DefaultHighlighter df2 = new DefaultHighlighter();
        txtL.setHighlighter(df2);
        char[] l = txtL.getText().toCharArray();
        char[] r = txtR.getText().toCharArray();

        try {
            for (int i = 0; i < Math.min(l.length, r.length); i++) {
                int start = i;
                for (; i < Math.min(l.length, r.length); i++);
                if (start != i) {
                    df1.addHighlight(start, i,
                        new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                    df2.addHighlight(start, i,
                        new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                }
            }
        } catch (BadLocationException | NullPointerException e) {
            e.printStackTrace();
        }
    }

    public boolean isHideCommonFormulas() {
        return actionHideCommonFormulas.isSelected();
    }

    public void setHideCommonFormulas(boolean hideCommonFormulas) {
        this.actionHideCommonFormulas.setEnabled(hideCommonFormulas);
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

    /*
     * private Component wrapScrollable(JComponent component, String title) { JPanel titlePanel =
     * new JPanel(new BorderLayout()); titlePanel.add(component);
     * titlePanel.setBorder(BorderFactory.createTitledBorder(title)); return new
     * JScrollPane(titlePanel); }
     */

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
                new ProofDifferenceView(left, left.parent(), mainWindow.getMediator());
            mainWindow.getDockControl().addDockable(pdv);
            pdv.setLocation(CLocation.base());
            pdv.setVisible(true);
        }
    }

    private class HideCommandFormulaAction extends KeyAction {
        private static final long serialVersionUID = -77545377028639666L;

        public HideCommandFormulaAction() {
            setName("Hide common formulas");
            setSelected(true);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            computeDifferences();
        }
    }
}
