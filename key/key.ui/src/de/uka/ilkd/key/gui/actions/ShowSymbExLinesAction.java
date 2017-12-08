package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Container;
import java.awt.Dialog;
import java.awt.event.ActionEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;

public class ShowSymbExLinesAction extends MainWindowAction {

    public ShowSymbExLinesAction(MainWindow mainWindow) {
        super(mainWindow);
        this.setName("Show Symbolic Execution Path");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Node node = getMediator().getSelectedNode();

        if (node == null) {
            return;
        }
        
        SourceElement activeStatement = node.getNodeInfo().getActiveStatement();
        if (activeStatement == null) {
            return;
        }
        String sourceFileStr = activeStatement.getPositionInfo().getParentClass();
        //String sourceFileStr = node.getNodeInfo().getExecStatementParentClass();
        
        if (!sourceFileStr.equals("<NONE>")) {
            
            System.out.println(sourceFileStr);

            final File sourceFile = new File(sourceFileStr);
            try {
                String source = IOUtil.readFrom(sourceFile);
                LineInformation[] li = IOUtil.computeLineInformation(sourceFile);

                final JDialog dialog = new JDialog(mainWindow, "Symbolic Execution Path of current Goal ",
                        Dialog.ModalityType.DOCUMENT_MODAL);
                dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);

                dialog.addKeyListener(new KeyAdapter() {
                    @Override
                    public void keyPressed(KeyEvent e) {
                        if (e.getKeyCode() == KeyEvent.VK_SPACE) {
                            dialog.dispose();
                        }
                    }
                });
                final JTextPane textPane = new JTextPane() {
                    @Override
                    public void addNotify() {
                        super.addNotify();
                        requestFocus();
                        //textAreaGoto(this, location.getLine(), location.getColumn());
                    }
                };
                
                textPane.addKeyListener(new KeyAdapter() {
                    @Override
                    public void keyPressed(KeyEvent e) {
                        if (e.getKeyCode() == KeyEvent.VK_SPACE) {
                            dialog.dispose();
                        }
                    }
                });
                
                textPane.setText(source);
                textPane.setFont(ExceptionDialog.MESSAGE_FONT);
                textPane.setEditable(false);
                
                StyledDocument doc = textPane.getStyledDocument();
                Style highlighted = textPane.addStyle("highlighted", null);
                StyleConstants.setBackground(highlighted, Color.YELLOW);
                
                Set<Integer> lines = constructLinesSet();
                for (Integer l : lines) {
                    // convert line numbers to offsets/lengths in the String 
                    int offset = li[l-1].getOffset();
                    int length = source.indexOf('\n', offset) - offset;
                    doc.setCharacterAttributes(offset, length, highlighted, true);
                    
                }                
                
                JScrollPane textPaneScrollPane = new JScrollPane(textPane);
                textPaneScrollPane 
                .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
                textPaneScrollPane
                .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

                Container container = dialog.getContentPane();
                container.add(textPane, BorderLayout.CENTER);

                dialog.pack();
                dialog.setVisible(true);

            }
            catch (IOException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
                return;
            }
        }
    }

    public Set<Integer> constructLinesSet() {
        Set<Integer> set = new HashSet<>();

        Node cur = getMediator().getSelectedNode();
        
        if (cur == null) {
            return null;
        }
        
        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                int startPos = activeStatement.getPositionInfo().getStartPosition().getLine();
                int endPos = activeStatement.getPositionInfo().getEndPosition().getLine();
                if (startPos != -1) {
                    if (startPos == endPos) {
                        set.add(startPos);
                        System.out.println("from/to " + startPos);
                    } else {
                        set.add(startPos);
                        set.add(endPos);
                        System.out.println("from " + startPos + " to " + endPos);
                    }
                }
            }
            cur = cur.parent();

        } while (cur != null);
        return set;
    }
}
