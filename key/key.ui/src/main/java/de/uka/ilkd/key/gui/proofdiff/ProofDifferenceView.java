package de.uka.ilkd.key.gui.proofdiff;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

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
    private final JPanel contentPanel;
    private final KeyAction actionHideCommonFormulas = new HideCommandFormulaAction();
    private final Services services;
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);
    private Node left, right;

    public ProofDifferenceView(Node left, Node right, Services services) {
        super(NullMultipleCDockableFactory.NULL);
        this.services = services;
        setCloseable(true);
        setRemoveOnClose(true);

        /*Box boxLeftAntec = new Box(BoxLayout.Y_AXIS),
                boxRightAntec = new Box(BoxLayout.Y_AXIS),
                boxLeftSucc = new Box(BoxLayout.Y_AXIS),
                boxRightSucc = new Box(BoxLayout.Y_AXIS);*/

        LC lc = new LC()
                //.debug()
                .fillX()
                .gridGap("5px", "5px")
                .wrapAfter(2);

        AC cc = new AC()
                //.size("pref", 0, 1)
                .align("right", 0)
                .size("pref")
                //.fill(0, 1)
                .grow(1, 0, 1);

        AC rc = new AC();//.size("26pt");

        contentPanel = new JPanel();
        contentPanel.setLayout(new MigLayout(lc, cc, rc));

        getContentPane().setLayout(new BorderLayout());
        //JScrollPane jsp = new JScrollPane(contentPanel);
        add(contentPanel);

        JPanel pNorth = new JPanel();
        JLabel lblLeftNode = new JLabel("Left Node:");
        JLabel lblRightNode = new JLabel("Right Node:");
        JTextField txtLeftNode = new JTextField();
        JTextField txtRightNode = new JTextField();
        pNorth.add(lblLeftNode);
        pNorth.add(txtLeftNode);
        pNorth.add(lblRightNode);
        pNorth.add(txtRightNode);
        txtLeftNode.setEditable(false);
        txtRightNode.setEditable(false);
        addPropertyChangeListener(PROPERTY_LEFT_NODE, (evt) ->
                txtLeftNode.setText(String.valueOf(left.serialNr())));

        addPropertyChangeListener(PROPERTY_RIGHT_NODE, (evt) ->
                txtRightNode.setText(String.valueOf(right.serialNr())));

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
        Dimension max = new Dimension(
                Math.max(txtL.getWidth(), txtR.getWidth()),
                Math.max(txtL.getHeight(), txtR.getHeight()));
        txtR.setSize(max);
        txtL.setSize(max);
        txtR.setPreferredSize(max);
        txtL.setPreferredSize(max);
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

    public Node getLeft() {
        return left;
    }

    public void setLeft(Node left) {
        Node oldLeft = this.left;
        this.left = left;
        propertyChangeSupport.firePropertyChange(PROPERTY_LEFT_NODE, oldLeft, left);
    }

    public Node getRight() {
        return right;
    }

    public void setRight(Node right) {
        Node old = this.right;
        this.right = right;
        propertyChangeSupport.firePropertyChange(PROPERTY_RIGHT_NODE, old, right);
    }

    private void computeDifferences() {
        contentPanel.removeAll();
        ProofDifference pd = ProofDifference.create(services, left, right);
        fill(pd.getAntecPairs());
        JSeparator sep = new JSeparator(JSeparator.HORIZONTAL);
        sep.setForeground(Color.BLACK);
        sep.setBorder(BorderFactory.createLineBorder(Color.BLACK, 5));
        contentPanel.add(sep, new CC().span(2).growX().height("10").alignX("left"));
        fill(pd.getSuccPairs());
    }

    private void fill(List<ProofDifference.Matching> pairs/*, JPanel boxLeft, JPanel boxRight*/) {
        for (ProofDifference.Matching pair : pairs) {
            if (isHideCommonFormulas() || pair.distance > 0) { // skip formulas that have no differences
                JEditorPane txtL = createEditor(pair.left);
                JEditorPane txtR = createEditor(pair.right);
                txtL.setAlignmentX(Component.RIGHT_ALIGNMENT);
                //equaliseSize(txtL, txtR);
                //txtL.setRows(3);
                //txtR.setRows(3);
                //contentPanel.add(txtL, cc);
                //contentPanel.add(txtR, cc);
                //hightlightDifferences(txtL, txtR);
            }
        }
    }

    protected JEditorPane createEditor(String content) {
        JEditorPane je = new JEditorPane(EDITOR_TYPE, content != null ? content : "");
        //JTextArea je = new JTextArea(content);
        je.setEditable(false);
        je.setFont(UIManager.getDefaults().getFont(Config.KEY_FONT_SEQUENT_VIEW));
        JPanel textAreaPanel = new JPanel(new BorderLayout());//new MigLayout("wrap", "[grow,fill]", "[]"));
        textAreaPanel.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
        textAreaPanel.add(je);
        contentPanel.add(textAreaPanel, new CC().sizeGroup("abc", "abc"));
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
        private Node left;

        public OpenDifferenceWithParent(MainWindow mainWindow, Node node) {
            super(mainWindow);
            setName("Diff with parent");
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
        public HideCommandFormulaAction() {
            setName("Hide common formulas");
            setSelected(false);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
        }
    }
}
