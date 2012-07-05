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
            textArea.setText("<pre><b>Hello!</b> World</pre>");
            JScrollPane scroll = new JScrollPane(textArea);
            cp.add(scroll, BorderLayout.CENTER);
        }
        {
            JPanel bottom = new JPanel(new FlowLayout(FlowLayout.RIGHT));
            {
                this.from = new JTextField("", 5);
                bottom.add(new JLabel("Older node:"));
                bottom.add(from);
            }
            {
                this.to = new JTextField("", 5);
                bottom.add(new JLabel("Newer node:"));
                bottom.add(to);
            }
            {
                JButton go =  new JButton("Show diff");
                go.addActionListener(new ActionListener() {
                    @Override public void actionPerformed(ActionEvent e) {
                        showDiff();
                    }
                });
                bottom.add(go);
                getRootPane().setDefaultButton(go);
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
            setSize(500, 600);
        }
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
            sFrom = getProofNodeText(from.getText());
            sTo = getProofNodeText(to.getText());
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
                sb.append("<span style='background-color: #ff8080;text-decoration: line-through;'>").
                    append(toHtml(diff.text)).append("</span>");
                break;
            case INSERT:
                sb.append("<font style='background-color: #80ff80;'>").
                    append(toHtml(diff.text)).append("</font>");
                break;
            }
        }
        sb.append("</pre>");

        String string = sb.toString();

        textArea.setText(string);
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
    private String getProofNodeText(String nodeNumber) {

        Proof proof = mainWindow.getMediator().getProof();

        if(proof == null) {
            throw new IllegalArgumentException("There is no open proof!");
        }

        int number;
        try {
            number = Integer.parseInt(nodeNumber);
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException(nodeNumber + " is not a number");
        }

        Node node = findNode(proof.root(), number);

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
