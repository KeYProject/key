package de.uka.ilkd.key.gui.proofdiff;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class ProofDifferenceView extends DefaultMultipleCDockable {
    public static final String PROPERTY_LEFT_NODE = "left";
    public static final String PROPERTY_RIGHT_NODE = "right";
    private static final String EDITOR_TYPE = "plain/text";
    private final KeyAction actionHideCommonFormulas = new HideCommandFormulaAction();
    private final Services services;
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);
    //private final JSplitPane rootPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT, true);
    private Box rootPanel = new Box(BoxLayout.Y_AXIS);
    private Node left, right;

    public ProofDifferenceView(@Nonnull Node left, @Nonnull Node right, Services services) {
        super(NullMultipleCDockableFactory.NULL);
        this.services = services;
        setCloseable(true);
        setRemoveOnClose(true);
        addAction(HelpFacade.createHelpButton("Using%20Key/NodeDiff"));

        getContentPane().setLayout(new BorderLayout());

        /*rootPanel.setOneTouchExpandable(true);
        rootPanel.setDividerSize(10);
        rootPanel.setLeftComponent(new JLabel("left"));
        rootPanel.setRightComponent(new JLabel("right"));*/
        getContentPane().add(rootPanel, BorderLayout.CENTER);

        JPanel pNorth = new JPanel(new FlowLayout(FlowLayout.CENTER));
        Box pNorthLeft = new Box(BoxLayout.Y_AXIS);
        Box pNorthRight = new Box(BoxLayout.Y_AXIS);
        JLabel lblLeftNode = new JLabel("Left Node:");
        JLabel lblRightNode = new JLabel("Right Node:");
        JTextField txtLeftNode = new JTextField();
        JTextField txtRightNode = new JTextField();
        pNorthLeft.add(lblLeftNode);
        pNorthLeft.add(txtLeftNode);
        pNorthRight.add(lblRightNode);
        pNorthRight.add(txtRightNode);
        //txtLeftNode.setEditable(false);
        //txtRightNode.setEditable(false);
        txtRightNode.addActionListener(e -> setRight(findNode(txtRightNode.getText())));
        txtLeftNode.addActionListener(e -> setLeft(findNode(txtLeftNode.getText())));

        pNorth.add(pNorthLeft);
        pNorth.add(new JSeparator(JSeparator.VERTICAL));
        pNorth.add(pNorthRight);

        txtLeftNode.setText(String.valueOf(left.serialNr()));
        txtRightNode.setText(String.valueOf(right.serialNr()));

        addPropertyChangeListener(evt -> {
            rootPanel.removeAll();
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
        Dimension max = new Dimension(
                Math.max(txtL.getWidth(), txtR.getWidth()),
                Math.max(txtL.getHeight(), txtR.getHeight()));
        txtR.setSize(max);
        txtL.setSize(max);
        txtR.setPreferredSize(max);
        txtL.setPreferredSize(max);
    }

    private Node findNode(String text) {
        try {
            int serialNr = Integer.parseInt(text);
            return left.proof().findAny(n -> n.serialNr() == serialNr);
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
        if (left == null) return;
        Node oldLeft = this.left;
        this.left = left;
        propertyChangeSupport.firePropertyChange(PROPERTY_LEFT_NODE, oldLeft, left);
    }

    @Nonnull
    public Node getRight() {
        return right;
    }

    public void setRight(@Nullable Node right) {
        if (right == null) return;
        Node old = this.right;
        this.right = right;
        propertyChangeSupport.firePropertyChange(PROPERTY_RIGHT_NODE, old, right);
    }

    private void computeDifferences() {
        rootPanel.removeAll();

        ProofDifference pd = ProofDifference.create(services, left, right);
        rootPanel.add(
                fill("Antecedent Differences", pd.getAntecPairs()));

        rootPanel.add(
                fill("Succedent Differences", pd.getSuccPairs()));

        getContentPane().invalidate();
        getContentPane().revalidate();
        getContentPane().repaint();
        getContentPane().repaint();
        getContentPane().repaint();
    }

    private JComponent fill(String title, List<ProofDifference.Matching> pairs) {
        Box pane = new Box(BoxLayout.Y_AXIS);
        pane.setBorder(BorderFactory.createTitledBorder(title));

        for (ProofDifference.Matching pair : pairs) {
            // hideCommonFormulas --> distance != 0
            if (!isHideCommonFormulas() || pair.distance > 0) { // skip formulas that have no differences
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
                //txtL.setRows(3);
                //txtR.setRows(3);
                //rootPanel.add(txtL, cc);
                //rootPanel.add(txtR, cc);
                //hightlightDifferences(txtL, txtR);
            }
        }

        if (pane.getComponentCount() == 0)
            pane.add(new JLabel("No differences found"));

        return new JScrollPane(pane);
    }

    protected JEditorPane createEditor(String content) {
        JEditorPane je = new JEditorPane(EDITOR_TYPE, content != null ? content : "");
        //JTextArea je = new JTextArea(content);
        je.setEditable(false);
        je.setFont(UIManager.getDefaults().getFont(Config.KEY_FONT_SEQUENT_VIEW));
        JPanel textAreaPanel = new JPanel(new BorderLayout());
        textAreaPanel.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
        textAreaPanel.add(je);
        //rootPanel.add(textAreaPanel, new CC().sizeGroup("abc", "abc"));
        return je;
    }

    private void hightlightDifferences(JEditorPane txtL, JEditorPane txtR) {
        DefaultHighlighter df1 = new DefaultHighlighter();
        txtL.setHighlighter(df1);
        DefaultHighlighter df2 = new DefaultHighlighter();
        txtL.setHighlighter(df2);
        char[] l = txtL.getText().toCharArray();
        char[] r = txtR.getText().toCharArray();

        try {
            for (int i = 0; i < Math.min(l.length, r.length); i++) {
                int start = i;
                for (; i < Math.min(l.length, r.length); i++)
                    ;
                if (start != i) {
                    df1.addHighlight(start, i, new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                    df2.addHighlight(start, i, new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
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

    static class MyPanel extends JPanel implements Scrollable {
        private static final long serialVersionUID = -3046025680639399997L;

        MyPanel(LayoutManager layout) {
            super(layout);
        }

        public Dimension getPreferredScrollableViewportSize() {
            return getPreferredSize();
        }

        public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
            return 0;
        }

        public boolean getScrollableTracksViewportHeight() {
            return false;
        }

        public boolean getScrollableTracksViewportWidth() {
            return true;
        }

        public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
            return 0;
        }
    }

    /*private Component wrapScrollable(JComponent component, String title) {
        JPanel titlePanel = new JPanel(new BorderLayout());
        titlePanel.add(component);
        titlePanel.setBorder(BorderFactory.createTitledBorder(title));
        return new JScrollPane(titlePanel);
    }*/

    public static class OpenDifferenceWithParent extends MainWindowAction {

        private static final long serialVersionUID = -7820466004457781393L;

        private Node left;

        public OpenDifferenceWithParent(MainWindow mainWindow, Node node) {
            super(mainWindow);
            setName("Diff with Parent");
            setEnabled(node.parent() != null);
            this.left = node;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofDifferenceView pdv = new ProofDifferenceView(left, left.parent(),
                    mainWindow.getMediator().getServices());
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
