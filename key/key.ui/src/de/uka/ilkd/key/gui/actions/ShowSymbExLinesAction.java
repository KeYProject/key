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

import javax.swing.JCheckBox;
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
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
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
 * @author Wolfram Pfeifer
 */
public class ShowSymbExLinesAction extends MainWindowAction {
    /**
     * ToolTip for the textPanes containing the source code.
     */
    private static final String TEXTPANE_TOOLTIP = "Click on a highlighted line to jump to the "
            + "most recent occurrence of this line in symbolic execution.";

    /**
     * String to display in an empty source code textPane.
     */
    private static final String NO_SOURCE = "No source loaded.";

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
     * HashMap with all files (of the current proof!).
     */
    private HashMap<String, File> files = new HashMap<String, File>();
    private HashMap<String, String> hashes = new HashMap<String,String>();        // TODO: make proof independent
    private HashMap<String, String> sources = new HashMap<String,String>();

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<NodePosPair> lines;

    

    /**
     * This document performs syntax highlighting when strings are inserted.
     * However, when editing the document the highlighting is not updating correctly at the moment.
     *
     * @author Wolfram Pfeifer
     */
    public static class JavaDocument extends DefaultStyledDocument {       // TODO: separate this from action?
        private enum Mode {
            STRING,
            NORMAL,
            KEYWORD,
            COMMENT,
            LINE_COMMENT,
            LINE_JML,
            JAVADOC,
            ANNOTATION,
            JML,
            JML_KEYWORD;
        }
        
        private enum CommentState {
            NO,
            MAYBE,       // "/"
            COMMENT,     // "/*"
            LNECOMMENT,  // "//"
            MAYBEEND;    // "*"
        }
        /**
         * Regular expression character class for all chars which are delimiters
         * of keywords. \\Q ... \\E is used to escape all chars inside the class.
         */
        private static final String DELIM = "[\\Q .;{}[]\n\r()+-*/%!=<>?:~&|^@'\"\\E]";

        private SimpleAttributeSet annotation = new SimpleAttributeSet();
        private SimpleAttributeSet string = new SimpleAttributeSet();
        private SimpleAttributeSet normal = new SimpleAttributeSet();
        private SimpleAttributeSet keyword = new SimpleAttributeSet();
        private SimpleAttributeSet comment = new SimpleAttributeSet();
        private SimpleAttributeSet javadoc = new SimpleAttributeSet();
        private SimpleAttributeSet jml = new SimpleAttributeSet();
        private SimpleAttributeSet jmlkeyword = new SimpleAttributeSet();

        // taken from https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
        final String[] keywordArray = {
            "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char", "class",
            "continue", "default", "do", "double", "else", "enum", "extends", "final", "finally",
            "float", "for", "if", "implements", "import", "instanceof", "int", "interface", "long",
            "native", "new", "package", "private", "protected", "public", "return", "short",
            "static", "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
            "transient", "try", "void", "volatile", "while",
            "true", "false", "null"        // literals
            // "const", "goto" // reserved, but currently not used in Java
        };
        // TODO: Is there a better way to specify this (maybe in an external file)?
        final String[] jmlKeywordArray = {
            // other Java keywords
            "break", "case", "catch", "class", "const", "continue", "default", "do", "else",
            "extends", "false", "finally", "for", "goto", "if", "implements", "import",
            "instanceof", "interface", "label", "new", "null", "package", "return", "super",
            "switch", "this", "throw", "throws", "true", "try", "void", "while",
            // types:
            "boolean", "byte", "char", "double", "float", "int", "long", "short",
            "\\bigint", "\\locset", "\\real", "\\seq", "\\TYPE",
            // modifiers:
            "abstract", "code", "code_bigint_math", "code_java_math", "code_safe_math",
            "extract", "final", "ghost", "helper", "instance", "model", "native", "non_null",
            "nullable", "nullable_by_default", "private", "protected", "peer", "\\peer", "public",
            "pure", "rep", "\\rep", "spec_bigint_math", "spec_java_math", "spec_protected",
            "spec_public", "spec_safe_math", "static", "strictfp", "strictly_pure", "synchronized",
            "transient", "two_state", "uninitialized", "volatile",

            "no_state", "modifies", "erases", "modifiable", "returns", "break_behavior",
            "continue_behavior", "return_behavior",
            // special JML expressions:
            "\\constraint_for", "\\created", "\\disjoint", "\\duration", "\\everything",
            "\\exception", "\\exists", "\\forall", "\\fresh", "\\index", "\\invariant_for",
            "\\is_initialized", "\\itself", "\\lblneg", "\\lblpos", "\\lockset", "\\max",
            "\\measured_by", "\\min", "\\new_elems_fresh", "\\nonnullelements", "\\not_accessed",
            "\\not_assigned", "\\not_modified", "\\not_specified", "\\nothing", "\\num_of",
            "\\old", "\\only_assigned", "\\only_called", "\\only_captured", "\\pre", "\\product",
            "\\reach", "\\reachLocs", "\\result", "\\same", "\\seq_contains", "\\space",
            "\\static_constraint_for", "\\static_invariant_for", "\\strictly_nothing",
            "\\subset", "\\sum", "\\type", "\\typeof", "\\working_space", "\\values", "\\inv",
            // clause keywords:
            "accessible", "accessible_redundantly", "assert", "assert_redundantly", "assignable",
            "assignable_redundantly", "assume", "assume_redudantly", "breaks", "breaks_redundantly",
            "\\by", "callable", "callable_redundantly", "captures", "captures_redundantly",
            "continues", "continues_redundantly", "debug", "\\declassifies", "decreases",
            "decreases_redundantly", "decreasing", "decreasing_redundantly", "diverges",
            "determines", "diverges_redundantly", "duration", "duration_redundantly", "ensures",
            "ensures_redundantly", "\\erases", "forall", "for_example", "hence_by", "implies_that",
            "in", "in_redundantly", "\\into", "loop_invariant", "loop_invariant_redundantly",
            "measured_by", "measured_by_redundantly", "maintaining", "maintaining_redundantly",
            "maps", "maps_redundantly", "\\new_objects", "old", "refining", "represents",
            "requires", "set", "signals", "signals_only", "\\such_that", "unreachable", "when",
            "working_space",
            // "invariant-like" keywords
            "abrupt_behavior", "abrupt_behaviour", "also", "axiom", "behavior", "behaviour",
            "constraint", "exceptional_behavior", "exceptional_behaviour", "initially",
            "invariant", "model_behavior", "model_behaviour", "monitors_for", "normal_behavior",
            "normal_behaviour", "readable", "writable",
            // ADT functions:
            "\\seq_empty", "\\seq_def", "\\seq_singleton", "\\seq_get", "\\seq_put",
            "\\seq_reverse", "\\seq_length", "\\index_of", "\\seq_concat", "\\empty",
            "\\singleton", "\\set_union", "\\intersect", "\\set_minus", "\\all_fields",
            "\\infinite_union", "\\strictly_than_nothing"
        };

        private Map<String, SimpleAttributeSet> keywords =
                new HashMap<String, SimpleAttributeSet>(keywordArray.length);
        private Map<String, SimpleAttributeSet> JMLkeywords =
                new HashMap<String, SimpleAttributeSet>(jmlKeywordArray.length);

        /**
         * The current position of the parser in the inserted String.
         */
        private int currentPos = 0;

        /**
         * The start index of the current token in the inserted String.
         */
        private int tokenStart = 0;

        /**
         * The current token of the parser.
         */
        private String token = "";

        /* mode <-> state:
         * mode stores the environment in which the parser is
         * state stores information about the just recently parsed characters */
        //private int mode = NORMAL_MODE;
        private Mode mode = Mode.NORMAL;

        /**
         *  Stores the current comment state of the parser to recognize comments/comment ends.
         */
        private CommentState state = CommentState.NO;

        public JavaDocument () {
            // set the styles (as in eclipse default settings)
            StyleConstants.setBold(keyword, true);
            StyleConstants.setForeground(keyword, new Color(127, 0, 85));
            StyleConstants.setForeground(comment, new Color(63, 127, 95));
            StyleConstants.setForeground(javadoc, new Color(63, 95, 191));
            StyleConstants.setForeground(string, new Color(42, 0, 255));
            StyleConstants.setForeground(jml, new Color(255, 102, 0));
            StyleConstants.setForeground(jmlkeyword, new Color(255, 102, 0));
            StyleConstants.setBold(jmlkeyword, true);

            // fill the keyword hash maps
            for (String k : keywordArray) {
                keywords.put(k, keyword);
            }

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
                mode = Mode.JML;
            } else if (state == CommentState.LNECOMMENT) {      // "//@"
                state = CommentState.NO;
                mode = Mode.LINE_JML;
            } else if (mode == Mode.NORMAL
                    && state == CommentState.NO) {              // "@"
                mode = Mode.ANNOTATION;
                tokenStart = currentPos;
            }
        }

        private void checkLinefeed() throws BadLocationException {
            state = CommentState.NO;
            if (mode == Mode.LINE_COMMENT) {                    // "// ... \n"
                insertCommentString(token, tokenStart);
                mode = Mode.NORMAL;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == Mode.LINE_JML) {                 // "//@ ... \n"
                insertJMLString(token, tokenStart);
                mode = Mode.NORMAL;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == Mode.ANNOTATION) {               // "@ ... \n"
                insertAnnotation(token, tokenStart);
                mode = Mode.NORMAL;     // reset
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else if (mode == Mode.NORMAL) {                   // normal mode
                insertNormalString(token, tokenStart);
                token = "\n";             // reset token
                tokenStart = currentPos;
            } else {    // modes: JML, Comment, JavaDoc
                token += '\n';
            }
        }

        private void checkStar() throws BadLocationException {
            if (state == CommentState.MAYBE) {              // "/*"
             // insert what we have in this line so far
                insertNormalString(token.substring(0, token.length() - 1), tokenStart);
                token = "/*";
                tokenStart = currentPos - 1;
                state = CommentState.COMMENT;
                mode = Mode.COMMENT;
            } else if (state == CommentState.COMMENT) {     // "/**"
                // tokenStart should be already set here
                token = token + '*';
                state = CommentState.MAYBEEND;
                mode = Mode.JAVADOC;
            } else if (mode == Mode.COMMENT                 // "/* ... *"
                    || mode == Mode.JAVADOC                 // "/*@ ... *"
                    || mode == Mode.JML) {                  // "/** ... *"
                // tokenStart should be already set here
                token = token + '*';
                state = CommentState.MAYBEEND;
            }
        }

        private void checkSlash() throws BadLocationException {
            if (mode == Mode.NORMAL
                     && state == CommentState.NO) {          // "/"
                token = token + '/';
                state = CommentState.MAYBE;
            } else if (state == CommentState.MAYBE) {        // "//"
                // insert what we have in this line so far
                insertNormalString(token.substring(0, token.length() - 1), tokenStart);
                token = "//";
                tokenStart = currentPos - 1;
                state = CommentState.LNECOMMENT;
                mode = Mode.LINE_COMMENT;
            } else if (state == CommentState.MAYBEEND) {     // "/* ... */"
                token = token + '/';
                if (mode == Mode.COMMENT) {
                    insertCommentString(token, tokenStart);
                } else if (mode == Mode.JAVADOC) {
                    if (token.equals("/**/")) {            // "/**/" is no JavaDoc
                        insertCommentString(token, tokenStart);
                    } else {
                        insertJavadocString(token, tokenStart);
                    }
                } else if (mode == Mode.JML) {
                    insertJMLString(token, tokenStart);
                }
                state = CommentState.NO;
                mode = Mode.NORMAL;
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
        private void processChar(String str) throws BadLocationException {
            char strChar = str.charAt(0);

            switch (strChar) {
            case ('@'):
                checkAt();
                break;
            case '\n':  // TODO: different line endings? -> use System.lineSeparator()
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

        private void insertCommentString(String str, int pos) throws BadLocationException {
            // remove the old word and formatting
            this.remove(pos, str.length());
            super.insertString(pos, str, comment);
        }

        private void insertAnnotation(String str, int pos) throws BadLocationException {
            // remove the old word and formatting
            this.remove(pos, str.length());
            super.insertString(pos, str, annotation);
        }

        private void insertJavadocString(String str, int pos) throws BadLocationException {
            // remove the old word and formatting
            this.remove(pos, str.length());
            super.insertString(pos, str, javadoc);
        }

        private void insertJMLString(String str, int pos) throws BadLocationException {
            // remove the old word and formatting
            this.remove(pos, str.length());
            int offset = 0;
            String[] tokens = str.split("((?<=" + DELIM + ")|(?=" + DELIM + "))");
            for (String t : tokens) {
                if (JMLkeywords.containsKey(t)) {
                    super.insertString(pos + offset, t, jmlkeyword);
                } else {
                    super.insertString(pos + offset, t, jml);
                }
                offset += t.length();
            }
        }

        private void insertNormalString(String str, int pos) throws BadLocationException {
            // remove the old word and formatting
            this.remove(pos, str.length());
            int offset = 0;
            String[] tokens = str.split("((?<=" + DELIM + ")|(?=" + DELIM + "))");
            for (String t : tokens) {
                if (keywords.containsKey(t)) {
                    super.insertString(pos + offset, t, keyword);
                } else {
                    super.insertString(pos + offset, t, normal);
                }
                offset += t.length();
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
     * @author Wolfram Pfeifer
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
     * @author Wolfram Pfeifer
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

            // We use the same font as in SequentView for consistency.
            textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));

            textPane.setToolTipText(TEXTPANE_TOOLTIP);
            textPane.setEditable(false);

            // compare cached hash with a newly created
            String origHash = hashes.get(entry.getKey());
            String curHash = IOUtil.computeMD5(entry.getValue());
            if (!origHash.equals(curHash)) {
                //if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour()) {
                    JCheckBox checkbox = new JCheckBox("Don't show this message again");
                    Object[] message = { "The source code this proof refers to was changed. Since the proof still" +
                                         "refers to the old source, this old source code is still present in the" +
                                         "source view on the right.",
                            checkbox};
                    JOptionPane.showMessageDialog(mainWindow, message, 
                            "Source code changed!", JOptionPane.INFORMATION_MESSAGE);
                    /*ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                                .setNotifyLoadBehaviour(!checkbox.isSelected());
                    ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();*/
                //}
            }

            // adds a listener for each textPane which reacts to font size changes
            // TODO: how to remove unused listeners (applies to all anonymous listeners in this class)?
            // TODO: not really working?
            Config.DEFAULT.addConfigChangeListener(new ConfigChangeListener() {
                @Override
                public void configChanged(ConfigChangeEvent e) {
                    Font myFont = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
                    if (myFont != null) {
                        textPane.setFont(myFont);
                    } else {
                        Debug.out("KEY_PROOF_SEQUENT_VIEW_FONT not available, " +
                              "use standard font.");
                    }
                }
            });

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
        // get selected proof
        // get selected node
        // if proof changed clear tabs and refill them
        // else update highlights
        
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
                    || se instanceof Else           // TODO: additional elements, e.g. String declaration etc.
                    /*|| se instanceof LocalVariableDeclaration*/) {
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
