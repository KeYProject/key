package de.uka.ilkd.key.gui.actions;

import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextPane;
import javax.swing.JViewport;
import javax.swing.UIManager;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.Document;
import javax.swing.text.Highlighter.Highlight;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Debug;

/**
 * This action is responsible for showing the symbolic execution path of the currently selected
 * node. This is done by adding tabs containing the source code and highlighting the lines which
 * were symbolically executed in the path from the root node down to the current node.
 * In addition, by clicking on such a highlighted line the user can jump to the first node in the
 * proof tree where a statement from this line is symbolically executed.
 *
 * Editing the source code in the tabs is currently not supported.
 *
 * @author WP
 */
public class ShowSymbExLinesAction extends MainWindowAction {
    /**
     * ToolTip for the textPanes containing the source code.
     */
    private static final String TEXTPANE_TOOLTIP = "Click on a highlighted line to jump to the "
            + "first occurrence of this line in symbolic execution.";

    /**
     * String to display in an empty source code textPane.
     */
    private static final String NO_SOURCE = "No source loaded.";

    /**
     * The font for the JTextPane containing the source code.
     * We use the same font as in SequentView for consistency.
     */
    private static final Font SOURCE_FONT = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);    // TODO: make font scalable

    /**
     * Indicates how many spaces are inserted instead of one tab (used in source code window).
     */
    private static final int TAB_SIZE = 4;      // TODO: Is there a global setting for this?

    /**
     * The color of normal highlights in source code (yellow).
     */
    private static final Color NORMAL_HIGHLIGHT_COLOR = Color.YELLOW;

    /**
     * The color of the most recent highlight in source code (a light orange).
     */
    private static final Color MOST_RECENT_HIGHLIGHT_COLOR = new Color(255, 153, 0);

    /**
     * The container for the tabs containing source code.
     */
    private final JTabbedPane tabs;

    /**
     * The status bar for displaying information about the current proof branch.
     */
    private final JLabel sourceStatusBar;

    /**
     * HashMap with all files (of the current proof!).         // TODO: What if a file changes?
     */
    private HashMap<String, File> files = new HashMap<String, File>();
    private HashMap<String, String> hashes = new HashMap<String,String>();        // TODO: make proof independent
    private HashMap<String, String> sources = new HashMap<String,String>();
    boolean warningShown = false;

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<NodePosPair> lines;

    private enum CommentState {
        NO,
        MAYBE,       // "/"
        COMMENT,     // "/*"
        LNECOMMENT,  // "//"
        MAYBEEND;    // "*"
    }

    /**
     * This document performs syntax highlighting when strings are inserted.
     * However, when editing the document the highlighting is not updating correctly at the moment.
     *
     * @author Wolfram Pfeifer
     */
    public class JavaDocument extends DefaultStyledDocument {
        public final static int STRING_MODE = 10;
        public final static int NORMAL_MODE = 11;
        public final static int KEYWORD_MODE = 12;
        public final static int NUMBER_MODE = 13;
        public final static int COMMENT_MODE = 14;
        public final static int LINE_COMMENT_MODE = 15;
        public final static int LINE_JML_MODE = 16;
        public final static int JAVADOC_MODE = 17;
        public final static int ANNOTATION_MODE = 18;
        public final static int JML_MODE = 19;
        public final static int JML_KEYWORD_MODE = 20;

        // TODO: other delimiters?
        // "+-*/(){}[]%!^~.;?:&|<>=\"'\\n(space)");
        private final static String DELIM = "[ .;{}\\[\\]]";

        private SimpleAttributeSet annotation = new SimpleAttributeSet();
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

        // mode <-> state:
        // mode stores the environment in which the parser is
        // state stores information about the just recently parsed characters
        private int mode = NORMAL_MODE;
        // stores the current comment state of the parser
        CommentState state = CommentState.NO;
        // true if the last processed char was a backslash
        boolean escapeChar = false;
        String token = "";
        int tokenStart = 0;

        public JavaDocument () {
            // set the styles (as in eclipse default settings)
            StyleConstants.setBold(keyword, true);
            StyleConstants.setForeground(keyword, new Color(127, 0, 85));
            StyleConstants.setForeground(comment, new Color(63, 127, 95));
            StyleConstants.setForeground(javadoc, new Color(63, 95, 191));
            StyleConstants.setForeground(number, Color.BLACK);
            StyleConstants.setForeground(string, new Color(42, 0, 255));
            StyleConstants.setForeground(jml, new Color(255, 102, 0));
            StyleConstants.setForeground(jmlkeyword, new Color(255, 102, 0));
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
                "static", "volatile", "new", "abstract", "final"  // TODO: additional keywords?
            };
            for (String k : keywordArray) {
                keywords.put(k, keyword);
            }

            final String[] jmlKeywordArray = {
                "normal_behavior", "exceptional_behavior", "model_behavior",
                "normal_behaviour", "exceptional_behaviour", "model_behaviour",
                "ensures", "requires", "measured_by", "signals", "signals_only",
                "ghost", "model", "\\old", "\\result", "\\nothing",
                "\\forall", "\\exists", "accessible", "assignable", "invariant", "helper",
                "loop_invariant", "decreases"
            };
            for (String k : jmlKeywordArray) {
                JMLkeywords.put(k, jmlkeyword);
            }
        }

        /*
         * NORMAL_MODE:
         * each line is a separate token that is at inserting checked for contained keywords
         *
         * JML:
         * each JML block is a separate token
         */

        private void checkAt() {
            token = token + '@';
            if (state == CommentState.COMMENT) {                // "/*@"
                state = CommentState.NO;
                mode = JML_MODE;
            } else if (state == CommentState.LNECOMMENT) {      // "//@"
                state = CommentState.NO;
                mode = LINE_JML_MODE;
            } else if (mode == NORMAL_MODE
                    && state == CommentState.NO) {              // "@"
                mode = ANNOTATION_MODE;
                tokenStart = currentPos;
            }
        }

        private void checkLinefeed() {
            state = CommentState.NO;
            if (mode == LINE_COMMENT_MODE) {                    // "// ... \n"
                insertCommentString(token, tokenStart);
                mode = NORMAL_MODE;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == LINE_JML_MODE) {                 // "//@ ... \n"
                insertJMLString(token, tokenStart);
                mode = NORMAL_MODE;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == ANNOTATION_MODE) {               // "@ ... \n"
                insertAnnotation(token, tokenStart);
                mode = NORMAL_MODE;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == NORMAL_MODE) {                   // normal mode
                insertNormalString(token, tokenStart);
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else {    // modes: JML, Comment, JavaDoc
                token += '\n';
            }
        }

        private void checkStar() {
            if (state == CommentState.MAYBE) {              // "/*"
             // insert what we have in this line so far
                insertNormalString(token.substring(0,token.length()-1), tokenStart);
                token = "/*";
                tokenStart = currentPos - 1;
                state = CommentState.COMMENT;
                mode = COMMENT_MODE;
            } else if (state == CommentState.COMMENT) {     // "/**"
                // tokenStart should be already set here
                token = token + '*';
                state = CommentState.MAYBEEND;
                mode = JAVADOC_MODE;
            } else if (mode == COMMENT_MODE                 // "/* ... *"
                    || mode == JAVADOC_MODE                 // "/*@ ... *"
                    || mode == JML_MODE) {                  // "/** ... *"
                // tokenStart should be already set here
                token = token + '*';
                state = CommentState.MAYBEEND;
            }
        }

        private void checkSlash() {
            if (mode == NORMAL_MODE
                     && state == CommentState.NO) {          // "/"
                token = token + '/';
                state = CommentState.MAYBE;
            } else if (state == CommentState.MAYBE) {        // "//"
                // insert what we have in this line so far
                insertNormalString(token.substring(0,token.length()-1), tokenStart);
                token = "//";
                tokenStart = currentPos - 1;
                state = CommentState.LNECOMMENT;
                mode = LINE_COMMENT_MODE;
            } else if (state == CommentState.MAYBEEND) {     // "/* ... */"
                token = token + '/';
                if (mode == COMMENT_MODE) {
                    insertCommentString(token, tokenStart);
                } else if (mode == JAVADOC_MODE) {
                    if (token.equals("/**/")) {            // "/**/" is no JavaDoc
                        insertCommentString(token, tokenStart);
                    } else {
                        insertJavadocString(token, tokenStart);
                    }
                } else if (mode == JML_MODE) {
                    insertJMLString(token, tokenStart);
                }
                state = CommentState.NO;
                mode = NORMAL_MODE;
                token = "";             // reset token
                tokenStart = currentPos + 1;
            } else {
                // not NORMAL_MODE
                token += '/';
            }
        }

        private void checkQuote() {
            // TODO:
            state = CommentState.NO;
            token += '"';
        }

        private void checkOther(char c) {
            token += c;
            state = CommentState.NO;
        }

        private void checkDelimiter(char c) {
            token += c;
            state = CommentState.NO;
        }

        // TODO: bin/oct/hex literals, long literals, floats/doubles?
        private void checkDigit(char c) {
            token += c;
            state = CommentState.NO;
        }

        /*
         * special char combinations:
         * comment/javadoc/jml start
         * comment end
         * line comment
         * annotation
         * string
         * number
         *
         * check at every delimiter: keyword/jmlKeyword?
         */
        private void processChar(String str) {
            char strChar = str.charAt(0);
            //System.out.println("Token: " + token);
            switch (strChar) {
            case ('@'):
                checkAt();
                break;
            case '\n':  // TODO: different line endings?
                checkLinefeed();
                break;
            //case '\t':  // all tabs were replaced earlier!
            //    break;
            case '*':
                checkStar();
                break;
            case '/':
                checkSlash();
                break;
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                checkDigit(strChar);
                break;
            case '"':
                checkQuote();
                break;
            // keyword delimiters: +-*/(){}[]%!^~.;?:&|<>="'\n(space)
            case '+':
            case '-':
            //case '*':
            //case '/':
            case '(':
            case ')':
            case '[':
            case ']':
            case '{':
            case '}':
            case '%':
            case '!':
            case '^':
            case '~':
            case '&':
            case '|':
            case '.':
            case ':':
            case ';':
            case '?':
            case '<':
            case '>':
            case '=':
            case '\'':
            case ' ':
            //case '"':
            //case '\'':
            //case '\n':
                checkDelimiter(strChar);
                break;
            default:
                checkOther(strChar);
                break;
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

        private void insertAnnotation(String str, int pos) {
            try {
                // remove the old word and formatting
                this.remove(pos, str.length());
                super.insertString(pos, str, annotation);
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

        private void insertJMLString(String str, int pos) {
            try {
                // remove the old word and formatting
                this.remove(pos, str.length());
                int offset = 0;
                String[] tokens = str.split("((?<=" + DELIM + ")|(?=" + DELIM + "))");
                for (String t : tokens) {
                    System.out.println("Inserting " + t + " at " + (pos + offset));
                    if (JMLkeywords.containsKey(t)) {
                        super.insertString(pos + offset, t, jmlkeyword);
                    } else {
                        super.insertString(pos + offset, t, jml);
                    }
                    offset += t.length();
                }
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }

        private void insertNormalString(String str, int pos) {
            try {
                // remove the old word and formatting
                System.out.println("Trying to remove: pos = " + pos + ", str = " + str);
                this.remove(pos, str.length());
                int offset = 0;
                String[] tokens = str.split("((?<=" + DELIM + ")|(?=" + DELIM + "))");
                for (String t : tokens) {
                    System.out.println("Inserting " + t + " at " + (pos + offset));
                    if (keywords.containsKey(t)) {
                        super.insertString(pos + offset, t, keyword);
                    } else {
                        super.insertString(pos + offset, t, normal);
                    }
                    offset += t.length();
                }
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }

        @Override
        public void insertString(int offs, String str, AttributeSet a) throws BadLocationException {
            // insert the unformatted string as a placeholder
            super.insertString(offs, str, normal);

            int strLen = str.length();
            int endpos = offs + strLen;
            int strpos;
            // process char by char
            for (int i = offs; i < endpos; i++) {
                currentPos = i;
                strpos = i - offs;
                processChar(Character.toString(str.charAt(strpos)));
            }
            currentPos = offs;
        }
    }

    /**
     * Creates a new Action with the given MainWindow and adds change listeners.
     * @param mainWindow the MainWindow of the GUI
     */
    public ShowSymbExLinesAction(MainWindow mainWindow) {
        super(mainWindow);
        tabs = mainWindow.getSourceTabs();
        sourceStatusBar = mainWindow.getSourceStatusBar();
        setName("Show Symbolic Execution Path");

        // add a listener for changes in the proof tree
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            public void selectedNodeChanged(KeYSelectionEvent e) {
                updateGUI();
            }

            public void selectedProofChanged(KeYSelectionEvent e) {
                clearCaches();
                updateGUI();
            }
        });
    }

    /**
     * A small container for a PositionInfo and a corresponding Node (used to store the first Node
     * containing the statement at the specified position).
     *
     * @author WP
     */
    static class NodePosPair {
        /**
         * The Node.
         */
        public final Node node;

        /**
         * The PositionInfo.
         */
        public final PositionInfo pos;

        /**
         * Creates a new pair.
         * @param node the Node corresponding to the given PositionInfo
         * @param pos the PositionInfo
         */
        public NodePosPair(Node node, PositionInfo pos) {
            this.node = node;
            this.pos = pos;
        }
    }

    /**
     * This listener checks if a highlighted section is clicked. If true, a jump in the proof tree
     * to the first node containing the highlighted statement is performed.<br>
     * <b>Note:</b> No jumping down in the proof tree is possible. Implementing this would be
     * non-trivial, because it was not unique into which branch we would want to descent.
     *
     * @author WP
     */
    private class TextPaneMouseAdapter extends MouseAdapter {
        /**
         * The precalculated start indices of the lines. Used to compute the clicked line number.
         */
        final LineInformation[] li;

        /**
         * The Painter used for painting the highlights (except for the most recent one).
         */
        final HighlightPainter painter;

        /**
         * The JTextPane containing the source code.
         */
        final JTextPane textPane;

        /**
         * The filename of the file whose content is displayed in the JTextPane.
         */
        final String filename;

        public TextPaneMouseAdapter(JTextPane textPane, LineInformation[] li,
                HighlightPainter painter, String filename) {
            this.textPane = textPane;
            this.li = li;
            this.painter = painter;
            this.filename = filename;
        }

        /**
         * Checks if the given position is within a highlight.
         * @param pos the position to check
         * @return true if highlighted and false if not
         */
        private boolean isHighlighted(int pos) {
            Highlight[] hs = textPane.getHighlighter().getHighlights();
            for (Highlight h : hs) {
                // search for highlight by the same painter
                if (h.getPainter() == painter) {
                    // check if the position is within the highlighted range
                    if (h.getStartOffset() <= pos && h.getEndOffset() >= pos) {
                        return true;
                    }
                }
            }
            return false;
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            int pos = textPane.viewToModel(e.getPoint());
            if (isHighlighted(pos)) {
                int line = 0;
                // calculate the line number
                while (line < li.length - 1) {
                    if (li[line].getOffset() <= pos && pos < li[line + 1].getOffset()) {
                        break;
                    }
                    line++;
                }
                // jump in proof tree (get corresponding node from list)
                Node n = null;
                for (NodePosPair p : lines) {
                    if (p.pos.getStartPosition().getLine() == line + 1
                            && p.pos.getFileName().equals(filename)) {
                        n = p.node;
                        break;
                    }
                }
                if (n != null) {
                    getMediator().getSelectionModel().setSelectedNode(n);
                }
            }
        }
    }

    /**
     * Paints the highlights for symbolically executed lines. The most recently executed line is
     * highlighted with a different color.
     * @param textPane the JTextPane containing the source code
     * @param li precalculated start indices of the lines
     * @param filename the filename corresponding to the given JTextPane
     * @param hp the painter to use for highlighting
     */
    private void paintSymbExHighlights(JTextPane textPane, LineInformation[] li, String filename,
            HighlightPainter hp) {
        try {
            for (int i = 0; i < lines.size(); i++) {
                NodePosPair l = lines.get(i);
                if (filename.equals(l.pos.getFileName())) {
                    Range r = calculateLineRange(textPane,
                            li[l.pos.getStartPosition().getLine() - 1].getOffset());
                    // use a different color for most recent
                    if (i == 0) {
                        textPane.getHighlighter().addHighlight(r.start(), r.end(),
                                new DefaultHighlightPainter(MOST_RECENT_HIGHLIGHT_COLOR));
                    } else {
                        textPane.getHighlighter().addHighlight(r.start(), r.end(), hp);
                    }
                }
            }
        } catch (BadLocationException e) {
            Debug.out(e);
        }
    }

    /**
     * Paints the highlight for the line where the mouse pointer currently points to.
     * @param textPane the textPane to highlight lines
     * @param p the current position of the mouse pointer
     * @param tag the highlight to change
     */
    private static void paintSelectionHighlight(JTextPane textPane, Point p, Object tag) {
        Range r = calculateLineRange(textPane, p);
        try {
            textPane.getHighlighter().changeHighlight(tag, r.start(), r.end());
        } catch (BadLocationException e) {
            Debug.out(e);
        }
    }

    /**
     * Calculates the range of actual text (not whitespace) in the line under the given point.
     * @param textPane the JTextPane with the text
     * @param p the point to check
     * @return the range of text (may be empty if there is just whitespace in the line)
     */
    private static Range calculateLineRange(JTextPane textPane, Point p) {
        return calculateLineRange(textPane, textPane.viewToModel(p));
    }

    /**
     * Calculates the range of actual text (not whitespace) in the line containing the given
     * position.
     * @param textPane the JTextPane with the text
     * @param pos the position to check
     * @return the range of text (may be empty if there is just whitespace in the line)
     */
    private static Range calculateLineRange(JTextPane textPane, int pos) {
        Document doc = textPane.getDocument();
        String text = "";
        try {
            text = doc.getText(0, doc.getLength());
        } catch (BadLocationException e) {
            Debug.out(e);
        }

        // find line end
        int end = text.indexOf('\n', pos);
        end = end == -1 ? text.length() : end;      // last line?

        // find line start
        int start = text.lastIndexOf('\n', pos - 1);          // TODO: different line endings?
        start = start == -1 ? 0 : start;            // first line?

        // ignore whitespace at the beginning of the line
        while (start < text.length() && start < end && Character.isWhitespace(text.charAt(start))) {
            start++;
        }

        return new Range(start, end);
    }

    /**
     * Clears cached files, lines, and existing tabs.
     */
    private void clearCaches() {
        warningShown = false;
        files.clear();
        hashes.clear();
        sources.clear();
        lines = null;
        tabs.removeAll();
    }

    /**
     * Replaces each tab in the given String by TAB_SIZE spaces.
     * @param s the String to replace
     * @return the resulting String (without tabs)
     */
    private static String replaceTabs(String s) {
        // fill a new array with the specified amount of spaces
        char[] rep = new char[TAB_SIZE];
        for (int i = 0; i < rep.length; i++) {
            rep[i] = ' ';
        }
        return s.replace("\t", new String(rep));
    }

    /**
     * Initializes a new JTextPane with the source code from the file in the HashMap entry.
     * In addition, listeners are added and highlights are painted.
     * @param entry the HashMap entry containing the file
     */
    private void initTextPane(Entry<String, File> entry) {
        try {
            JTextPane textPane = new JTextPane();

            textPane.setFont(SOURCE_FONT);
            textPane.setToolTipText(TEXTPANE_TOOLTIP);
            textPane.setEditable(false);

            // compare cached hash with a newly created
            String origHash = hashes.get(entry.getKey());
            String curHash = IOUtil.computeMD5(entry.getValue());
            if (!origHash.equals(curHash)) {
                //textPane.setBackground(new Color(255, 128, 128));
                //textPane.setToolTipText("<html><b>Attention! </b>Source code was changed since start of the proof!<br><br>"
                //        + TEXTPANE_TOOLTIP + "</html>");
                if (!warningShown) {        // show warning only once (TODO: per proof)
                    JOptionPane.showMessageDialog(mainWindow,
                            "The source code this proof was started from has changed in the background.\n"
                            + "However, the proof refers to the old version of the source code "
                            + "(as shown in the window on the right).",
                            "Source code changed!", JOptionPane.INFORMATION_MESSAGE);
                    warningShown = true;
                }
            }

            //String original = IOUtil.readFrom(entry.getValue());
            String original = sources.get(entry.getKey());
            String source = replaceTabs(original);  // replace all tabs by spaces

            // use input stream here to compute line information of the string with replaced tabs
            InputStream inStream = new ByteArrayInputStream(source.getBytes());
            LineInformation[] li = IOUtil.computeLineInformation(inStream);


            JavaDocument doc = new JavaDocument();
            textPane.setDocument(doc);
            doc.insertString(0, source, new SimpleAttributeSet());

            // add a listener to highlight the line currently pointed to
            Object selectionHL = textPane.getHighlighter().addHighlight(0, 0,
                    new DefaultHighlightPainter(DEFAULT_HIGHLIGHT_COLOR));
            textPane.addMouseMotionListener(new MouseMotionListener() {
                @Override
                public void mouseMoved(MouseEvent e) {
                    paintSelectionHighlight(textPane, e.getPoint(), selectionHL);
                }

                @Override
                public void mouseDragged(MouseEvent e) {
                }
            });

            // paint the highlights (symbolically executed lines) for this file
            HighlightPainter hp = new DefaultHighlightPainter(NORMAL_HIGHLIGHT_COLOR);
            paintSymbExHighlights(textPane, li, entry.getKey(), hp);

            textPane.addMouseListener(new TextPaneMouseAdapter(textPane, li, hp,
                    entry.getKey()));

            /* for each File, create a Tab in TabbedPane
             * (additional panel is needed to prevent line wrapping) */
            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            JScrollPane textScrollPane = new JScrollPane();
            textScrollPane.setViewportView(nowrap);
            textScrollPane.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            textScrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);
            tabs.addTab(entry.getValue().getName(), textScrollPane);

            // add the full path as tooltip for the tab
            int index = tabs.indexOfTab(entry.getValue().getName());
            tabs.setToolTipTextAt(index, entry.getValue().getAbsolutePath());
        } catch (IOException e) {
            Debug.out("An error occurred while reading " + entry.getValue().getAbsolutePath(), e);
        } catch (BadLocationException e) {
            Debug.out(e);
        }
    }

    /**
     * Fills the HashMaps containing Files and translations from lines (in source code) to
     * corresponding nodes in proof tree.
     */
    private void fillMaps() {
        for (NodePosPair p : lines) {
            PositionInfo l = p.pos;
            File f = new File(l.getFileName());
            if (files.putIfAbsent(l.getFileName(), f) == null) {
                try {
                    hashes.put(l.getFileName(), IOUtil.computeMD5(f));
                    sources.put(l.getFileName(), IOUtil.readFrom(f));
                } catch (IOException e) {
                    Debug.out("Unknown IOException!", e);
                }
            }
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        updateGUI();
    }

    /**
     * Performs an update of the GUI:
     * <ul>
     *      <li>updates the TabbedPane with the source files used</li>
     *      <li>highlights the symbolically executed lines</li>
     *      <li>updates the source status bar of the main window with information about the current
     *          branch</li>
     * </ul>
     */
    private void updateGUI() {
        Node symbExNode = getMediator().getSelectedNode();
        tabs.removeAll();

        if (symbExNode == null) {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
            return;
        }

        // get PositionInfo of all symbEx nodes
        lines = constructLinesSet(symbExNode);
        if (lines == null) {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
            return;
        }

        fillMaps();
        
        // create and initialize a new TextPane for every file
        for (Entry<String, File> entry : files.entrySet()) {
            initTextPane(entry);
        }
        if (tabs.getTabCount() > 0) {
            tabs.setBorder(new EmptyBorder(0, 0, 0, 0));

            // activate the tab with the most recent file
            PositionInfo p = lines.isEmpty() ? null : lines.getFirst().pos;
            if (p != null) {
                File f = files.get(p.getFileName());
                String s = f.getName();
                for (int i = 0; i < tabs.getTabCount(); i++) {
                    if (tabs.getTitleAt(i).equals(s)) {
                        tabs.setSelectedIndex(i);

                        // scroll to most recent highlight
                        int line = lines.getFirst().pos.getEndPosition().getLine();
                        scrollNestedTextPaneToLine(tabs.getComponent(i), line, f);
                    }
                }
            }
        } else {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
        }
        // set the path information in the status bar
        sourceStatusBar.setText(collectPathInformation(symbExNode));
    }

    /**
     * Looks for a nested JTextPane in the component of the JTabbedPane.
     * If it exists, JTextPane is scrolled to the given line.
     * @param comp the component of a JTabbedPane
     * @param line the line to scroll to
     * @param f the file of the JTextPane
     */
    private void scrollNestedTextPaneToLine(Component comp, int line, File f) {
        if (comp instanceof JScrollPane) {
            JScrollPane sp = (JScrollPane)comp;
            if (sp.getComponent(0) instanceof JViewport) {
                JViewport vp = (JViewport)sp.getComponent(0);
                if (vp.getComponent(0) instanceof JPanel) {
                    JPanel panel = (JPanel)vp.getComponent(0);
                    if (panel.getComponent(0) instanceof JTextPane) {
                        JTextPane tp = (JTextPane)panel.getComponent(0);
                        try {
                            String original = IOUtil.readFrom(f);
                            String source = replaceTabs(original);  // replace all tabs by spaces

                            /* use input stream here to compute line information of the string with
                             * replaced tabs
                             */
                            InputStream inStream = new ByteArrayInputStream(source.getBytes());
                            LineInformation[] li = IOUtil.computeLineInformation(inStream);
                            int offs = li[line].getOffset();
                            tp.setCaretPosition(offs);
                        } catch (IOException e) {
                            e.printStackTrace();
                        }
                    }
                }
            }
        }
    }

    /**
     * Collects the set of lines to highlight starting from the given node in the proof tree.
     * @param cur the given node
     * @return a linked list of pairs of PositionInfo objects containing the start and end
     * positions for the highlighting and Nodes.
     */
    private static LinkedList<NodePosPair> constructLinesSet(Node cur) {
        LinkedList<NodePosPair> list = new LinkedList<NodePosPair>();

        if (cur == null) {
            return null;
        }

        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                if (activeStatement instanceof SourceElement) {
                    PositionInfo pos = joinPositionsRec((SourceElement)activeStatement);

                    // we are only interested in well defined PositionInfo objects with a file name
                    if (pos != null && !pos.equals(PositionInfo.UNDEFINED) && pos.startEndValid()
                            && pos.getFileName() != null) {
                        list.addLast(new NodePosPair(cur, pos));
                    }
                }
            }
            cur = cur.parent();

        } while (cur != null);
        return list;
    }

    /**
     * Joins all PositionInfo objects of the given SourceElement and its children.
     * @param se the given SourceElement
     * @return a new PositionInfo starting at the minimum of all the contained positions and
     * ending at the maximum position
     */
    private static PositionInfo joinPositionsRec(SourceElement se) {
        if (se instanceof NonTerminalProgramElement) {
            if (se instanceof If
                    || se instanceof Then
                    || se instanceof Else
                    || se instanceof LocalVariableDeclaration) {
                return PositionInfo.UNDEFINED;
            }

            NonTerminalProgramElement ntpe = (NonTerminalProgramElement)se;
            PositionInfo pos = se.getPositionInfo();

            for (int i = 0; i < ntpe.getChildCount(); i++) {
                ProgramElement pe2 = ntpe.getChildAt(i);
                pos = PositionInfo.join(pos, joinPositionsRec(pe2));
            }
            return pos;
        } else {
            return se.getPositionInfo();
        }
    }

    /**
     * Collects the information from the tree to which branch the current node belongs:
     * <ul>
     *      <li>Invariant Initially Valid</li>
     *      <li>Body Preserves Invariant</li>
     *      <li>Use Case</li>
     *      <li>...</li>
     * </ul>
     * @param node the current node
     * @return a String containing the path information to display
     */
    private String collectPathInformation(Node node) {

        while (node != null) {
            if (node.getNodeInfo() != null && node.getNodeInfo().getBranchLabel() != null) {
                String label = node.getNodeInfo().getBranchLabel();
                if (label.equals("Invariant Initially Valid")
                        || label.equals("Invariant Preserved and Used")
                        || label.equals("Body Preserves Invariant")
                        || label.equals("Use Case")
                        || label.equals("Use Axiom")
                        || label.equals("Show Axiom Satisfiability")
                        || label.contains("Normal Execution")
                        || label.contains("Null Reference")
                        //|| label.contains("Postcondition")  // TODO:
                        //|| label.contains("Assignable")
                        || label.contains("Index Out of Bounds")) {
                    return label;
                }
            }
            node = node.parent();
        }
        // if no label was found we have to prove the postcondition
        return "Show Postcondition/Assignable clause";
    }
}
