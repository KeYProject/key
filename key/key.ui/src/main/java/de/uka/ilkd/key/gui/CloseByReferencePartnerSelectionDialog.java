package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.EtchedBorder;
import javax.swing.text.html.HTMLDocument;
import java.awt.*;
import java.awt.event.*;
import java.util.List;

/**
 * A simple dialog to select a reference partner from a list of candidates. Shows the sequent and
 * a combo box to select the partner node. The list of potential partners must be determined
 * externally.
 *
 * @author Wolfram Pfeifer
 */
public class CloseByReferencePartnerSelectionDialog extends JDialog {
    /** initial size of the dialog */
    private static final Dimension INITIAL_SIZE = new Dimension(900, 450);

    /** The font for the JEditorPane. Should resemble the standard font of KeY for proofs etc. */
    private static final Font TXT_AREA_FONT = new Font(Font.MONOSPACED, Font.PLAIN, 14);

    /** The partner node finally selected by the user. Null if the dialog was canceled. */
    private Node selectedNode;

    /**
     * Renders a Node to a string by using its serial number.
     */
    private static class NodeRenderer extends JLabel implements ListCellRenderer<Node> {
        @Override
        public Component getListCellRendererComponent(JList<? extends Node> list, Node value,
                                                      int index, boolean isSelected,
                                                      boolean cellHasFocus) {
            setText("Node " + value.serialNr());

            // this is necessary to make setBackground effective
            setOpaque(true);
            if (isSelected) {
                setBackground(list.getSelectionBackground());
                setForeground(list.getSelectionForeground());
            } else {
                setBackground(list.getBackground());
                setForeground(list.getForeground());
            }
            return this;
        }
    }

    /**
     * Creates a new dialog for selecting the node to refer to.
     * @param goal the goal that shall be closed by reference
     * @param potentialPartners The list of potential partners. These partners must be closed, must
     *                          have the same sequent, and must have (at least) all hidden formulas
     *                          which are present in the given goal.
     */
    public CloseByReferencePartnerSelectionDialog(Goal goal, List<Node> potentialPartners) {
        super(MainWindow.getInstance(), "Choose a reference partner", true);

        JEditorPane sequentPane = new JEditorPane();
        sequentPane.setEditable(false);
        sequentPane.setContentType("text/html");

        // set font for sequent pane
        String cssRule = "body { font-family: " + TXT_AREA_FONT.getFamily() + "; "
                              + "font-size: " + TXT_AREA_FONT.getSize() + "pt; }";
        ((HTMLDocument) sequentPane.getDocument()).getStyleSheet().addRule(cssRule);

        sequentPane.setText(LogicPrinter.quickPrintSequent(goal.sequent(),
                                                           goal.proof().getServices()));
        JScrollPane scrollPane = new JScrollPane(sequentPane);

        JPanel upper = new JPanel();
        upper.setBorder(BorderFactory.createTitledBorder(
            BorderFactory.createEtchedBorder(EtchedBorder.LOWERED), "Sequent"));
        upper.setLayout(new BorderLayout());
        upper.add(scrollPane);

        JComboBox<Node> nodeSelectionCBox = new JComboBox<>();
        nodeSelectionCBox.setRenderer(new NodeRenderer());
        nodeSelectionCBox.setModel(new DefaultComboBoxModel<>(
            potentialPartners.toArray(new Node[0])));

        JPanel center = new JPanel();
        center.setBorder(BorderFactory.createTitledBorder(
            BorderFactory.createEtchedBorder(EtchedBorder.LOWERED),
                                        "Potential Reference Partners"));
        center.add(nodeSelectionCBox);

        JButton buttonOK = new JButton("OK");
        getRootPane().setDefaultButton(buttonOK);
        buttonOK.addActionListener(e -> {
            selectedNode = (Node) nodeSelectionCBox.getSelectedItem();
            dispose();
        });

        JButton buttonCancel = new JButton("Cancel");
        buttonCancel.addActionListener(e -> dispose());

        JPanel buttons = new JPanel();
        buttons.add(buttonOK);
        buttons.add(buttonCancel);

        JPanel lower = new JPanel();
        lower.setLayout(new BoxLayout(lower, BoxLayout.Y_AXIS));
        lower.add(center);
        lower.add(buttons);

        // we want to give the sequent as much space as possible, therefore we assign it to CENTER
        getContentPane().add(upper, BorderLayout.CENTER);
        getContentPane().add(lower, BorderLayout.SOUTH);
        setSize(INITIAL_SIZE);

        // dispose when cross is clicked
        setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
        addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                dispose();
            }
        });

        // dispose on ESCAPE
        getRootPane().registerKeyboardAction(
            e -> dispose(), KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        // center over MainWindow
        setLocationRelativeTo(MainWindow.getInstance());
    }

    public Node getSelectedNode() {
        return selectedNode;
    }
}
