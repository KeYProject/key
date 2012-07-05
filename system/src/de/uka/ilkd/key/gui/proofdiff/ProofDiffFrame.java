package de.uka.ilkd.key.gui.proofdiff;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.UIManager;
import javax.swing.WindowConstants;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.proofdiff.diff_match_patch.Diff;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.Proof;

/**
 * Proof-of-concept implementation of a textual sequent comparison.
 * 
 * This class provides a frame which allows the user to display a in-place comparison of two
 * sequents. The comparison happens on the pretty-printed text only, no sophisticated tree
 * comparison. The algorithm is taken from a google library.
 * 
 * @see diff_match_patch
 * @author mattias ulbrich
 */

@SuppressWarnings("serial")
public class ProofDiffFrame extends JFrame {

    /**
     * The action to show a new frame of this class. Is used in {@link MainWindow}.
     */
    public static class Action extends AbstractAction {

        private final MainWindow mainWindow;

        public Action(MainWindow mainWindow) {
            this.mainWindow = mainWindow;
            putValue(NAME, "Visual node diff ...");
            // putValue(SMALL_ICON, ...);
            putValue(SHORT_DESCRIPTION, "Open a new proof node diff window.");
        }

        @Override 
        public void actionPerformed(ActionEvent e) {
            ProofDiffFrame pdf = new ProofDiffFrame(mainWindow);
            pdf.setLocationRelativeTo(mainWindow);
            pdf.setVisible(true);
        }

    }

    /**
     * The text area display the diff'ed text.
     */
    private JEditorPane textArea;

    /**
     * The textfield holding the lower comparison number.
     */
    private JTextField from;

    /**
     * The textfield holding the upper comparison number.
     */
    private JTextField to;

    /**
     * The main window. This is how we access the {@link Proof} object.
     */
    private final MainWindow mainWindow;

    /**
     * Instantiates a new proof-diff frame.
     * 
     * @param mainWindow
     *            the main window of the system
     */
    public ProofDiffFrame(MainWindow mainWindow) {
        super("Visual Diff between two sequents");
        this.mainWindow = mainWindow;
        guiInit();
    }

    /**
     * initialize the user interface
     */
    private void guiInit() {
        Container cp = getContentPane();
        setLayout(new BorderLayout());
        {
            this.textArea = new JEditorPane();
            textArea.setContentType("text/html");
            Font myFont = UIManager.getFont(Config.KEY_FONT_CURRENT_GOAL_VIEW);
            textArea.setFont(myFont);
            //            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 14));
            textArea.setEditable(false);
            //            textArea.setText("<pre><b>Hello!</b> World</pre>");
            JScrollPane scroll = new JScrollPane(textArea);
            cp.add(scroll, BorderLayout.CENTER);
        }
        {
            JPanel bottom = new JPanel(new FlowLayout(FlowLayout.RIGHT));
            {
                this.from = new JTextField("", 5);
                from.setToolTipText("Set the parent node to compare. May be empty for the direct predecessor");
                bottom.add(new JLabel("Older node:"));
                bottom.add(from);
            }
            {
                this.to = new JTextField("", 5);
                to.setToolTipText("Set the child node to compare. Must not be empty");
                bottom.add(new JLabel("Newer node:"));
                bottom.add(to);
            }
            {
                JButton go =  new JButton("Show diff");
                go.setToolTipText("Show difference between the two nodes specified here.");
                go.addActionListener(new ActionListener() {
                    @Override public void actionPerformed(ActionEvent e) {
                        showDiff();
                    }
                });
                bottom.add(go);
                getRootPane().setDefaultButton(go);
            }
            {
                JButton last = new JButton("Show selected node");
                last.setToolTipText("Show difference introduced by the rule application leading to the selected node");
                last.addActionListener(new ActionListener() {
                    @Override public void actionPerformed(ActionEvent e) {
                        setSelectedNode();
                        showDiff();
                    }
                });
                bottom.add(last);
            }
            {
                JButton close = new JButton("Close");
                close.addActionListener(new ActionListener() {
                    @Override public void actionPerformed(ActionEvent e) {
                        ProofDiffFrame.this.setVisible(false);
                    }
                });
                bottom.add(close);
            }
            cp.add(bottom, BorderLayout.SOUTH);
            setSize(700, 600);
        }
    }

    /**
     * Sets the to field to the selected node.
     * Clears the fom field.
     */
    private void setSelectedNode() {

        Node node = mainWindow.getMediator().getSelectedNode();
        if(node == null) {
            throw new IllegalArgumentException("There is no selected proof node!");
        }

        from.setText("");
        to.setText(Integer.toString(node.serialNr()));
    }

    /**
     * Initiate a diff calculation and set the content of the text area.
     * 
     * It uses the result of {@link diff_match_patch#diff_main(String, String, boolean)}
     * and html markup to show the text.
     */
    private void showDiff() {
        String sFrom;
        String sTo;

        try {
            int toNo;
            String toText = to.getText();
            if(toText.length() == 0) {
                throw new IllegalArgumentException("At least the second proof node must be specified");
            } else {
                toNo = Integer.parseInt(to.getText());
                sTo = getProofNodeText(toNo);
            }

            String fromText = from.getText();
            if(fromText.length() == 0) {
                sFrom = getProofNodeText(getParent(toNo));
            } else {
                int fromNo = Integer.parseInt(fromText);
                sFrom = getProofNodeText(fromNo);
            }
        } catch (NumberFormatException e) {
            JOptionPane.showMessageDialog(null, "This is not a number: " + e.getMessage(), 
                    "Error", JOptionPane.ERROR_MESSAGE);
            return;
        } catch (IllegalArgumentException e) {
            JOptionPane.showMessageDialog(null, e.getMessage(), "Error", JOptionPane.ERROR_MESSAGE);
            return;
        }

        LinkedList<Diff> diffs = new diff_match_patch().diff_main(sFrom, sTo, false);

        StringBuilder sb = new StringBuilder();
        sb.append("<pre>");
        for (Diff diff : diffs) {
            switch (diff.operation) {
            case EQUAL:
                sb.append(toHtml(diff.text));
                break;
            case DELETE:
                if(onlySpaces(diff.text)) {
                    sb.append(diff.text);
                } else {
                    sb.append("<span style='background-color: #ff8080;text-decoration: line-through;'>").
                    append(toHtml(diff.text)).append("</span>");
                }
                break;
            case INSERT:
                if(onlySpaces(diff.text)) {
                    sb.append(diff.text);
                } else {
                    sb.append("<font style='background-color: #80ff80;'>").
                    append(toHtml(diff.text)).append("</font>");
                }
                break;
            }
        }
        sb.append("</pre>");

        String string = sb.toString();

        textArea.setText(string);
    }

    private boolean onlySpaces(CharSequence text) {
        for (int i = 0; i < text.length(); i++) {
            if(!Character.isWhitespace(text.charAt(i))) {
                return false;
            }
        }
        return true;
    }

    private int getParent(int no) {
        Proof proof = mainWindow.getMediator().getProof();
        if(proof == null) {
            throw new IllegalArgumentException("There is no open proof!");
        }

        Node node = findNode(proof.root(), no);
        if(node == null) {
            throw new IllegalArgumentException(no + " is not a node in the proof");
        }

        Node parent = node.parent();
        if(parent == null) {
            throw new IllegalArgumentException(no + " has no parent node");
        }

        return parent.serialNr();
    }

    /**
     * Render special html characters and spaces and new lines
     * 
     * @param string
     *            an arbitrary string
     * @return the string converted to html
     */
    private String toHtml(String string) {
        string = string.replace("&", "&amp;");
        string = string.replace("<", "&lt;");
        string = string.replace(">", "&gt;");
        string = string.replace(" ", "&nbsp;");
        string = string.replace("\n", "<br/>");
        return string;
    }

    /**
     * Gets the pretty printed node text for a node.
     * 
     * @param nodeNumber
     *            the number of the node to search
     * @return the proof node text
     * @throws IllegalArgumentException
     *             if the number string is bad or there is no proof.
     */
    private String getProofNodeText(int nodeNumber) {

        Proof proof = mainWindow.getMediator().getProof();

        if(proof == null) {
            throw new IllegalArgumentException("There is no open proof!");
        }

        Node node = findNode(proof.root(), nodeNumber);

        if(node == null) {
            throw new IllegalArgumentException(nodeNumber + " does not denote a valid node");
        }

        LogicPrinter logicPrinter = 
                new LogicPrinter(new ProgramPrinter(null), 
                        new NotationInfo(),
                        proof.getServices(),
                        true);

        node.sequent().prettyprint(logicPrinter);

        return logicPrinter.result().toString();
    }



    // This must have been implemented already, somewhere
    private Node findNode(Node node, int number) {
        if(node.serialNr() == number) {
            return node;
        }

        NodeIterator it = node.childrenIterator();
        while(it.hasNext()) {
            Node n = it.next();
            if(n.serialNr() <= number) {
                Node result = findNode(n, number);
                if(result != null)
                    return result;
            }
        }

        return null;
    }

    public static void main(String[] args) {
        ProofDiffFrame pdf = new ProofDiffFrame(null);
        pdf.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
        pdf.setSize(500,500);
        pdf.setVisible(true);
    }
}
