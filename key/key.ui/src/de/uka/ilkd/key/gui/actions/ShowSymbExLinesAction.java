package de.uka.ilkd.key.gui.actions;

import java.awt.Color;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import javax.swing.JTabbedPane;
import javax.swing.JTextPane;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.Element;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
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
    
    public class JavaDocument extends DefaultStyledDocument {
        
        private SimpleAttributeSet string = new SimpleAttributeSet();
        private SimpleAttributeSet normal = new SimpleAttributeSet();
        private SimpleAttributeSet keyword = new SimpleAttributeSet();
        private SimpleAttributeSet number = new SimpleAttributeSet();
        private SimpleAttributeSet comment = new SimpleAttributeSet();
        private SimpleAttributeSet javadoc = new SimpleAttributeSet();
        private SimpleAttributeSet jml = new SimpleAttributeSet();
        private SimpleAttributeSet jmlkeyword = new SimpleAttributeSet();
        
        private Map<String, SimpleAttributeSet> keywords = new HashMap<String, SimpleAttributeSet>();
        private Map<String, SimpleAttributeSet> JMLkeywords = new HashMap<String, SimpleAttributeSet>();
        
        private int currentPos = 0;
        private int mode = NORMAL_MODE;
        
        public final static int STRING_MODE = 10;
        public final static int NORMAL_MODE = 11;
        public final static int KEYWORD_MODE = 12;
        public final static int NUMBER_MODE = 13;
        public final static int COMMENT_MODE = 14;
        public final static int LINE_COMMENT_MODE = 15;
        public final static int JAVADOC_MODE = 16;
        public final static int ANNOTATION_MODE = 17;
        public final static int JML_MODE = 18;
        public final static int JML_KEYWORD_MODE = 19;
        
        public JavaDocument () {
            StyleConstants.setBold(keyword, true);
            StyleConstants.setForeground(keyword, new Color(127, 0, 85));
            StyleConstants.setForeground(comment, new Color(0, 180, 0));
            StyleConstants.setForeground(javadoc, new Color(0, 50, 255));
            StyleConstants.setForeground(number, Color.RED);
            StyleConstants.setForeground(string, Color.BLUE);
            StyleConstants.setForeground(jml, Color.ORANGE);
            StyleConstants.setForeground(jmlkeyword, Color.ORANGE);
            StyleConstants.setBold(jmlkeyword, true);
            
            final String[] keywordArray = {"package", "class", "import", "interface", "enum",
                    "extends", "implements",
                    "public", "protected", "private",
                    "byte", "int", "long", "char", "float", "double", "boolean", "void",
                    "true", "false",
                    "this", "super", "null",
                    "if", "else", "for", "while", "do", "switch", "case", "break", "continue",
                    "return",
                    "try", "catch", "finally",
                    "static", "volatile", "new", "abstract", "final"  // TODO: 
            };
            for (String k : keywordArray) {
                keywords.put(k, keyword);
            }
            
            final String[] JMLkeywordArray = {"normal_behavior", "exceptional_behavior", "model_behavior",
                    "ensures", "requires", "measured_by", "signals", "signals_only",
                    "ghost", "model", "\\old", "\\result", "\\nothing",
                    "\\forall", "\\exists", "accessible", "assignable", "invariant", "helper"
                    
            };
            for (String k : JMLkeywordArray) {
                JMLkeywords.put(k, jmlkeyword);
            }
        }
        
        private void checkForComment() {
            int offs = this.currentPos;
            Element element = this.getParagraphElement(offs);
            String elementText = "";
            try {
                // this gets our chuck of current text for the element we're on
                elementText = this.getText(element.getStartOffset(), element
                        .getEndOffset()
                        - element.getStartOffset());
            } catch (Exception ex) {
                // whoops!
                System.out.println("no text");
            }
            int strLen = elementText.length();
            if (strLen == 0) {
                return;
            }
            int i = 0;
     
            if (element.getStartOffset() > 0) {
                // translates backward if neccessary
                offs = offs - element.getStartOffset();
            }
            if ((offs >= 1) && (offs <= strLen - 1)) {
                i = offs;
                char commentStartChar1 = elementText.charAt(i - 1);
                char commentStartChar2 = elementText.charAt(i);
                if (mode == COMMENT_MODE && commentStartChar1 == '*'
                        && commentStartChar2 == '*') {
                    mode = JAVADOC_MODE;
                    this.insertJavadocString("/**", currentPos - 2);
                } else if (commentStartChar1 == '/' && commentStartChar2 == '*') {
                    mode = COMMENT_MODE;
                    this.insertCommentString("/*", currentPos - 1);
                } else if (commentStartChar1 == '/' && commentStartChar2 == '/') {
                    mode = LINE_COMMENT_MODE;
                    this.insertCommentString("//", currentPos - 1);
                } else if (commentStartChar1 == '*' && commentStartChar2 == '/') {
                    boolean javadoc = false;
                    if (mode == JAVADOC_MODE) {
                        javadoc = true;
                    }
                    mode = NORMAL_MODE;
                    if (javadoc) {
                        //this.insertJavadocString("*/", currentPos - 1);
                    } else {
                        this.insertCommentString("*/", currentPos - 1);
                    }
                }
     
            }
        }
        
        private void checkForKeyword() {
            if (mode != NORMAL_MODE && mode != JML_MODE) {
                return;
            }
            int offs = this.currentPos;
            Element element = this.getParagraphElement(offs);
            String elementText = "";
            try {
                // this gets our chuck of current text for the element we're on
                elementText = this.getText(element.getStartOffset(), element
                        .getEndOffset()
                        - element.getStartOffset());
            } catch (Exception ex) {
                // whoops!
                System.out.println("no text");
            }
            int strLen = elementText.length();
            if (strLen == 0) {
                return;
            }
            int i = 0;
     
            if (element.getStartOffset() > 0) {
                // translates backward if neccessary
                offs = offs - element.getStartOffset();
            }
            if ((offs >= 0) && (offs <= strLen - 1)) {
                i = offs;
                while (i > 0) {
                    // the while loop walks back until we hit a delimiter
                    i--;
                    char charAt = elementText.charAt(i);
                    if ((charAt == ' ') | (i == 0) | (charAt == '(')
                            | (charAt == ')') | (charAt == '{') | (charAt == '}')) { // if i
                        // == 0
                        // then
                        // we're
                        // at
                        // the
                        // begininng
                        if (i != 0) {
                            i++;
                        }
                        String word = elementText.substring(i, offs);// skip the period
     
                        String s = word.trim().toLowerCase();
                        // this is what actually checks for a matching keyword
                        if (mode == NORMAL_MODE && keywords.containsKey(s) ||
                                mode == JML_MODE && JMLkeywords.containsKey(s)) {
                            insertKeyword(word, currentPos, keywords.get(s));
                        }
                        break;
                    }
                }
            }
        }
        
        private void processChar(String str) {
            char strChar = str.charAt(0);
            if (mode != COMMENT_MODE && mode != LINE_COMMENT_MODE
                    && mode != JAVADOC_MODE && mode != ANNOTATION_MODE) {
                mode = NORMAL_MODE;
            }
            switch (strChar) {
            case ('@'):
                if (mode == NORMAL_MODE) {
                    mode = ANNOTATION_MODE;
                }
                break;
            case ('{'):
            case ('}'):
            case (' '):
            case ('\n'):
            case ('('):
            case (')'):
            case (';'):
            case ('.'): {
                checkForKeyword();
                if (mode == ANNOTATION_MODE && strChar == '(') {
                    mode = NORMAL_MODE;
                }
                if ((mode == STRING_MODE || mode == LINE_COMMENT_MODE || mode == ANNOTATION_MODE)
                        && strChar == '\n') {
                    mode = NORMAL_MODE;
                }
            }
                break;
            case ('"'): {
                //insertTextString(str, currentPos);
                //this.checkForString();
            }
            break;
            case ('0'):
            case ('1'):
            case ('2'):
            case ('3'):
            case ('4'):
            case ('5'):
            case ('6'):
            case ('7'):
            case ('8'):
            case ('9'): {
                //checkForNumber();
            }
            break;
            case ('*'):
            case ('/'): {
                checkForComment();
            }
            break;
            }
            if (mode == NORMAL_MODE) {
                //this.checkForString();
            }
            if (mode == STRING_MODE) {
                //insertTextString(str, this.currentPos);
            } else if (mode == NUMBER_MODE) {
                //insertNumberString(str, this.currentPos);
            } else if (mode == COMMENT_MODE) {
                insertCommentString(str, this.currentPos);
            } else if (mode == LINE_COMMENT_MODE) {
                insertCommentString(str, this.currentPos);
            } else if (mode == JAVADOC_MODE) {
                insertJavadocString(str, this.currentPos);
            } else if (mode == ANNOTATION_MODE) {
                //insertAnnotationString(str, this.currentPos);
            }
     
        }
        
        private void insertCommentString(String str, int pos) {
            try {
                // remove the old word and formatting
                this.remove(pos, str.length());
                super.insertString(pos, str, comment);
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }
        
        private void insertKeyword(String str, int pos, AttributeSet as) {
            try {
                // remove the old word and formatting
                this.remove(pos - str.length(), str.length());
                /*
                 * replace it with the same word, but new formatting we MUST call
                 * the super class insertString method here, otherwise we would end
                 * up in an infinite loop !!
                 */
                super.insertString(pos - str.length(), str, as);
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }
     
        private void insertJavadocString(String str, int pos) {
            try {
                // remove the old word and formatting
                this.remove(pos, str.length());
                super.insertString(pos, str, javadoc);
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }
        
        @Override
        public void insertString(int offs, String str, AttributeSet a) throws BadLocationException {
            super.insertString(offs, str, normal);
            
            int strLen = str.length();
            int endpos = offs + strLen;
            int strpos;
            for (int i = offs; i < endpos; i++) {
                currentPos = i;
                strpos = i - offs;
                processChar( Character.toString(str.charAt(strpos)));
            }
            currentPos = offs;
        }
    }

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
            // TODO: NPE here with SumAndMax (maybe l has no filename?)
            m.putIfAbsent(l.getFileName(), new File(l.getFileName()));
        }

        final JTabbedPane tabs = mainWindow.getSourceTabs();
        tabs.removeAll();

        for (Entry<String, File> l : m.entrySet()) {
            final JTextPane textPane = new JTextPane();

            try {
                String source = IOUtil.readFrom(l.getValue());
                //textPane.setText(source);
                LineInformation[] li = IOUtil.computeLineInformation(l.getValue());

                textPane.setFont(ExceptionDialog.MESSAGE_FONT);
                textPane.setFont(new Font("Courier New", Font.PLAIN, 16));
                textPane.setEditable(true);

                JavaDocument doc = new JavaDocument();
                textPane.setDocument(doc);
                doc.insertString(0, source, new SimpleAttributeSet());
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

                        doc.setCharacterAttributes(startIndex, length, i, false);
                    }
                }

                // for each File, create a Tab in TabbedPane
                tabs.addTab(l.getKey(), textPane);
            } catch (IOException e1) {
                e1.printStackTrace();
            }
            catch (BadLocationException e1) {
                // TODO Auto-generated catch block
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
