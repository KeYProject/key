package de.uka.ilkd.key.gui.actions;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map.Entry;
import javax.swing.JTabbedPane;
import javax.swing.JTextPane;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;

public class ShowSymbExLinesAction extends MainWindowAction {

    public ShowSymbExLinesAction(MainWindow mainWindow) {
        super(mainWindow);
        this.setName("Show Symbolic Execution Path");

        // add a listener for changes in the proof tree
        final KeYSelectionListener selListener = new KeYSelectionListener() {

            public void selectedNodeChanged(KeYSelectionEvent e) {
                actionPerformed(null);  // TODO: null
            }

            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };
        getMediator().addKeYSelectionListener(selListener);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Node symbExNode = getMediator().getSelectedNode();

        if (symbExNode == null) {
            return;
        }

        // get PositionInfo of all symbEx nodes
        LinkedList<PositionInfo> lines = constructLinesSet(symbExNode);
        if (lines == null) {
            return;
        }

        // get Files from PositionInfos
        HashMap<String, File> m = new HashMap<String, File>();

        boolean firstHighlighted = false;
        for (PositionInfo l : lines) {
            if (!firstHighlighted) {
                System.out.println("first: " + l);
                firstHighlighted = true;
            } else {
                System.out.println(l);
            }
            m.putIfAbsent(l.getFileName(), new File(l.getFileName()));
        }

        final JTabbedPane tabs = mainWindow.getSourceTabs();
        tabs.removeAll();

        for (Entry<String, File> l : m.entrySet()) {
            final JTextPane textPane = new JTextPane();

            try {
                String source = IOUtil.readFrom(l.getValue());
                textPane.setText(source);
                LineInformation[] li = IOUtil.computeLineInformation(l.getValue());

                textPane.setFont(ExceptionDialog.MESSAGE_FONT);
                textPane.setEditable(false);

                StyledDocument doc = textPane.getStyledDocument();
                Style highlighted = textPane.addStyle("highlighted", null);
                StyleConstants.setBackground(highlighted, Color.YELLOW);
                int styles = lines.size();
                int curr = styles;

                // for each PositionInfo, highlight the corresponding lines in the corresponding file
                for (PositionInfo pos : lines) {
                    if (pos.getFileName().equals(l.getKey())) { // TODO: overhead!
                        // convert line numbers to offsets/lengths in the String
                        Position start = pos.getStartPosition();
                        Position end = pos.getEndPosition();
                        // TODO: Position doc: first line is line 1, first column is column 1
                        int startIndex = li[start.getLine()-1].getOffset() + start.getColumn()-1;    // TODO: shifting necessary?
                        int endIndex = li[end.getLine()-1].getOffset() + end.getColumn()-1;
                        int length = endIndex - startIndex + 1;
                        System.out.println("start: " + startIndex + " end: " + endIndex + " length: " + length);

                        // more recent lines have a more saturated color
                        Style i = textPane.addStyle(Integer.toString(curr), null);
                        StyleConstants.setBackground(i, new Color(255, 255, 255 - 255 / styles * curr--));

                        doc.setCharacterAttributes(startIndex, length, i, true);
                    }
                }

                // for each File, create a Tab in TabbedPane
                tabs.addTab(l.getKey(), textPane);
            } catch (IOException e1) {
                e1.printStackTrace();
            }
        }
        if (tabs.getTabCount() > 0) {
            tabs.setBorder(new EmptyBorder(0, 0, 0, 0));
        } else {
            tabs.setBorder(new TitledBorder("No source loaded"));
        }
    }

    public LinkedList<PositionInfo> constructLinesSet(Node cur) {
        LinkedList<PositionInfo> list = new LinkedList<PositionInfo>();

        if (cur == null) {
            return null;
        }

        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                PositionInfo pos = activeStatement.getPositionInfo();
                if (pos != null && !pos.equals(PositionInfo.UNDEFINED)) {
                    list.addLast(pos);
                }
            }
            cur = cur.parent();

        } while (cur != null);
        return list;
    }
}
