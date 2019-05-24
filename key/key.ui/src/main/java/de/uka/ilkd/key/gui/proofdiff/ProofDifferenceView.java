package de.uka.ilkd.key.gui.proofdiff;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class ProofDifferenceView extends DefaultMultipleCDockable {
    /**
     * Threshold for maximum levensthein distant.
     */
    private static final int THRESHOLD = 25;
    private static final String EDITOR_TYPE = "plain/text";
    private final Node left, right;
    private final JPanel contentPanel;
    private int line = 0;

    public ProofDifferenceView(Node left, Node right, Services services) {
        super(NullMultipleCDockableFactory.NULL);
        this.left = left;
        this.right = right;

        setTitleText("Difference between: " + left.serialNr() + " and " + right.serialNr());
        setCloseable(true);
        setRemoveOnClose(true);

        /*Box boxLeftAntec = new Box(BoxLayout.Y_AXIS),
                boxRightAntec = new Box(BoxLayout.Y_AXIS),
                boxLeftSucc = new Box(BoxLayout.Y_AXIS),
                boxRightSucc = new Box(BoxLayout.Y_AXIS);*/

        LC lc = new LC().fillX().gridGap("5px", "5px").wrapAfter(2);
        AC cc = new AC().grow(1, 0, 1).fill(0, 1);
        AC rc = new AC();
        contentPanel = new JPanel();
        contentPanel.setLayout(new MigLayout(lc, cc, rc));
        /*JPanel boxLeftAntec = new JPanel(new MigLayout(lc, cc)),
                boxRightAntec = new JPanel(new MigLayout(lc, cc)),
                boxLeftSucc = new JPanel(new MigLayout(lc, cc)),
                boxRightSucc = new JPanel(new MigLayout(lc, cc));*/

        ProofDifference pd = ProofDifference.create(services, left, right);

        fill(pd.getAntecPairs());
        //boxLeftAntec, boxRightAntec);

        JSeparator sep = new JSeparator();
        sep.setBorder(BorderFactory.createLineBorder(Color.BLACK, 5));
        contentPanel.add(sep, "span 2");

        fill(pd.getSuccPairs());
        //boxLeftSucc, boxRightSucc);

        /*JSplitPane splitAntec = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, boxLeftAntec, boxRightAntec);
        JSplitPane splitSucc = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, boxLeftSucc, boxRightSucc);
        JSplitPane splitSequent = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                wrapScrollable(splitAntec, "Antecedent"),
                wrapScrollable(splitSucc, "Succedent"));

        splitAntec.setDividerLocation(.5);
        splitSequent.setDividerLocation(.5);
        splitSucc.setDividerLocation(.5);

        splitAntec.setOneTouchExpandable(true);
        splitSequent.setOneTouchExpandable(true);
        splitSucc.setOneTouchExpandable(true);*/
        getContentPane().setLayout(new BorderLayout());
        add(new JScrollPane(contentPanel));
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

    private void fill(List<Pair<String, String>> pairs/*, JPanel boxLeft, JPanel boxRight*/) {
        for (Pair<String, String> pair : pairs) {
            JTextArea txtL = createEditor(pair.first);
            JTextArea txtR = createEditor(pair.second);
            //equaliseSize(txtL, txtR);
            //hightlightDifferences(txtL, txtR);
            txtL.setRows(3);
            txtR.setRows(3);
            CC cc = new CC().sizeGroupY("abc" + (++line));
            contentPanel.add(txtL, cc);
            contentPanel.add(txtR, cc);
        }
    }

    protected JTextArea createEditor(String content) {
        //JEditorPane je = new JEditorPane(EDITOR_TYPE, content != null ? content : "");
        JTextArea je = new JTextArea(content);
        je.setEditable(false);
        je.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
        je.setFont(UIManager.getDefaults().getFont(Config.KEY_FONT_SEQUENT_VIEW));
        return je;
    }

    private void hightlightDifferences(JEditorPane txtL, JEditorPane txtR) {
        return;/*
        DefaultHighlighter df1 = new DefaultHighlighter();
        txtL.setHighlighter(df1);
        DefaultHighlighter df2= new DefaultHighlighter();
        txtL.setHighlighter(df2);
        char[] l = txtL.getText().toCharArray();
        char[] r = txtR.getText().toCharArray();
        try {
            for (int i = 0; i < Math.min(l.length, r.length); i++) {
                if (l[i] != r[i]) {
                    df1.addHighlight(i, i + 1, new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                    df2.addHighlight(i, i + 1, new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                }
            }
        } catch (BadLocationException e) {
            e.printStackTrace();
        }*/

    }

    private Component wrapScrollable(JComponent component, String title) {
        JPanel titlePanel = new JPanel(new BorderLayout());
        titlePanel.add(component);
        titlePanel.setBorder(BorderFactory.createTitledBorder(title));
        return new JScrollPane(titlePanel);
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
            ProofDifferenceView pdv = new ProofDifferenceView(left, left.parent(),
                    mainWindow.getMediator().getServices());
            mainWindow.getDockControl().addDockable(pdv);
            pdv.setLocation(CLocation.base());
            pdv.setVisible(true);
        }
    }
}
