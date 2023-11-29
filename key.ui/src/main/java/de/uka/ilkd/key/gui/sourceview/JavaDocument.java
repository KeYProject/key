/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;

import java.awt.Color;
import java.beans.PropertyChangeListener;
import java.io.Serial;
import java.util.*;
import java.util.regex.Pattern;
import javax.swing.text.*;

import de.uka.ilkd.key.gui.colors.ColorSettings;

import static de.uka.ilkd.key.speclang.jml.JMLUtils.isJmlCommentStarter;

/**
 * This document performs syntax highlighting when strings are inserted. However, only inserting the
 * whole String at once is supported, otherwise the syntax highlighting will be faulty.
 * <p>
 * Note that tab characters have to be replaced by spaces before inserting into the document.
 * <p>
 * The document currently only works when newlines are represented by "\n"!
 *
 * @author Wolfram Pfeifer
 */
public class JavaDocument extends DefaultStyledDocument {

    @Serial
    private static final long serialVersionUID = -1856296532743892931L;

    // highlighting colors (same as in HTMLSyntaxHighlighter of SequentView for consistency)

    /** highight color for Java keywords (dark red/violet) */
    private static final ColorSettings.ColorProperty JAVA_KEYWORD_COLOR =
        ColorSettings.define("[java]keyword", "", new Color(0x7f0055));

    // private static final Color JAVA_STRING_COLOR = new Color(0x000000);

    /** highight color for comments (dull green) */
    private static final ColorSettings.ColorProperty COMMENT_COLOR =
        ColorSettings.define("[java]comment", "", new Color(0x3f7f5f));

    /** highight color for JavaDoc (dull green) */
    private static final ColorSettings.ColorProperty JAVADOC_COLOR =
        ColorSettings.define("[java]javadoc", "", new Color(0x3f7f5f));

    /** highight color for JML (dark blue) */
    private static final ColorSettings.ColorProperty JML_COLOR =
        ColorSettings.define("[java]jml", "", new Color(0x0000c0));

    /** highight color for JML keywords (blue) */
    private static final ColorSettings.ColorProperty JML_KEYWORD_COLOR =
        ColorSettings.define("[java]jmlKeyword", "", new Color(0x0000f0));

    /**
     * Enum to indicate the current mode (environment) of the parser. Examples are STRING ("..."),
     * COMMENT (&#47;&#42; ... &#42;&#47;), JML (&#47;&#42;&#64; ... &#42;&#47; ), ...
     */
    private enum Mode {
        /* parser is currently inside a String */
        // STRING, // currently not in use
        /** parser is currently inside normal java code */
        NORMAL,
        /** parser is currently inside a keyword */
        KEYWORD,
        /** parser is currently inside a comment (starting with "&#47;&#42;") */
        COMMENT,
        /** parser is currently inside a line comment (starting with "&#47;&#47;") */
        LINE_COMMENT,
        /** parser is currently inside a line JML annotation (starting with "&#47;&#47;&#64;") */
        LINE_JML,
        /** parser is currently inside JavaDoc (starting with "&#47;&#42;&#42;") */
        JAVADOC,
        /** parser is currently inside an annotation (starting with "&#64;") */
        ANNOTATION,
        /** parser is currently inside a JML annotation (starting with "&#47;&#42;&#64;") */
        JML,
        /** parser is currently inside a JML keyword */
        JML_KEYWORD
    }

    /**
     * Enum to indicate the current comment state of the parser. It is used to store which comment
     * relevant chars were just recently encountered.
     */
    private enum CommentState {
        /** no comment char encountered */
        NO,
        /** last processed char was "&#47;" */
        MAYBE,
        /** last processed chars were "&#47;&#42;" */
        COMMENT,
        /** last processed chars were "&#47;&#47;" */
        LINECOMMENT,
        /**
         * current token could be a JML annotation marker (see JML reference manual 4.4,
         * <a href="http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC29">
         * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC29</a>)
         */
        JML_ANNOTATION,
        /**
         * current token could be a JML annotation marker inside single line JML (see JML reference
         * manual 4.4,
         * <a href="http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC29">
         * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC29</a>)
         */
        JML_ANNOTATION_LINE,
        /** last processed char was "&#42;" */
        MAYBEEND
    }

    /**
     * Regular expression character class for all chars which are delimiters of keywords. \\Q ...
     * \\E is used to escape all chars inside the class.
     */
    private static final String DELIM = "[\\Q .;{}[]\n\r()+-*/%!=<>?:~&|^@'\"\\E]";

    /** Pattern to match JML start with annotation marker(s). */
    private static final Pattern JML_ANNOT_MARKER = Pattern.compile("/\\*([+|-][$_a-zA-Z0-9]+)+@");

    /** Pattern to match single line JML start with annotation marker(s). */
    private static final Pattern JML_ANNOT_MARKER_LINE =
        Pattern.compile("//([+|-][$_a-zA-Z0-9]+)+@");

    /**
     * Stores the Java keywords which have to be highlighted. The list is taken from
     * <a href="https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html">
     * https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html </a>.
     * <p>
     * To add additional keywords, simply add them to the array. Note that the keywords must not
     * contain any of the characters defined by the DELIM regex.
     */
    private static final String[] KEYWORDS = { "abstract", "assert", "boolean", "break", "byte",
        "case", "catch", "char", "class", "continue", "default", "do", "double", "else", "enum",
        "extends", "final", "finally", "float", "for", "if", "implements", "import", "instanceof",
        "int", "interface", "long", "native", "new", "package", "private", "protected", "public",
        "return", "short", "static", "strictfp", "super", "switch", "synchronized", "this", "throw",
        "throws", "transient", "try", "void", "volatile", "while", "true", "false", "null"
            // "const", "goto" // reserved, but currently not used in Java
    };

    /**
     * Stores the JML keywords which have to be highlighted.
     * <p>
     * To add additional keywords, simply add them to the array. Note that the keywords must not
     * contain any of the characters defined by the DELIM regex.
     */
    private static final String[] JMLKEYWORDS = {
        // other Java keywords
        "break", "case", "catch", "class", "const", "continue", "default", "do", "else", "extends",
        "false", "finally", "for", "goto", "if", "implements", "import", "instanceof", "interface",
        "label", "new", "null", "package", "return", "super", "switch", "this", "throw", "throws",
        "true", "try", "void", "while",
        // types:
        "boolean", "byte", "char", "double", "float", "int", "long", "short", "\\bigint",
        "\\locset", "\\real", "\\seq", "\\TYPE",
        // modifiers:
        "abstract", "code", "code_bigint_math", "code_java_math", "code_safe_math", "extract",
        "final", "ghost", "helper", "instance", "model", "native", "non_null", "nullable",
        "nullable_by_default", "private", "protected", "peer", "\\peer", "public", "pure", "rep",
        "\\rep", "spec_bigint_math", "spec_java_math", "spec_protected", "spec_public",
        "spec_safe_math", "static", "strictfp", "strictly_pure", "synchronized", "transient",
        "two_state", "uninitialized", "volatile",

        "no_state", "modifies", "erases", "modifiable", "returns", "break_behavior",
        "continue_behavior", "return_behavior",
        // special JML expressions:
        "\\constraint_for", "\\created", "\\disjoint", "\\duration", "\\everything", "\\exception",
        "\\exists", "\\forall", "\\fresh", "\\index", "\\invariant_for", "\\is_initialized",
        "\\itself", "\\lblneg", "\\lblpos", "\\lockset", "\\max", "\\measured_by", "\\min",
        "\\new_elems_fresh", "\\nonnullelements", "\\not_accessed", "\\not_assigned",
        "\\not_modified", "\\not_specified", "\\nothing", "\\num_of", "\\old", "\\only_assigned",
        "\\only_called", "\\only_captured", "\\pre", "\\product", "\\reach", "\\reachLocs",
        "\\result", "\\same", "\\seq_contains", "\\space", "\\static_constraint_for",
        "\\static_invariant_for", "\\strictly_nothing", "\\subset", "\\sum", "\\type", "\\typeof",
        "\\working_space", "\\values", "\\inv",
        // clause keywords:
        "accessible", "accessible_redundantly", "assert", "assert_redundantly", "assignable",
        "assignable_free", "assignable_redundantly", "assigns", "assigns_free",
        "assigns_redundantly", "assigning", "assigning_free", "assigning_redundantly",
        "loop_modifies", "loop_modifies_free", "loop_modifies_redundantly", "loop_writes",
        "loop_writes_free", "loop_writes_redundantly", "assume", "assume_redudantly", "breaks",
        "breaks_redundantly", "\\by", "callable", "callable_redundantly", "captures",
        "captures_redundantly", "continues", "continues_redundantly", "debug", "\\declassifies",
        "decreases", "decreases_redundantly", "decreasing", "decreasing_redundantly", "diverges",
        "determines", "diverges_redundantly", "duration", "duration_redundantly", "ensures",
        "ensures_free", "ensures_redundantly", "\\erases", "forall", "for_example", "hence_by",
        "implies_that", "in", "in_redundantly", "\\into", "loop_invariant", "loop_invariant_free",
        "loop_invariant_redundantly", "measured_by", "measured_by_redundantly", "maintaining",
        "maintaining_redundantly", "maps", "maps_redundantly", "\\new_objects", "old", "refining",
        "represents", "requires", "requires_free", "set", "signals", "signals_only", "\\such_that",
        "unreachable", "when", "working_space",
        // "invariant-like" keywords
        "abrupt_behavior", "abrupt_behaviour", "also", "axiom", "behavior", "behaviour",
        "constraint", "exceptional_behavior", "exceptional_behaviour", "initially", "invariant",
        "invariant_free", "model_behavior", "model_behaviour", "monitors_for", "normal_behavior",
        "normal_behaviour", "readable", "writable",
        // ADT functions:
        "\\seq_empty", "\\seq_def", "\\seq_singleton", "\\seq_get", "\\seq_put", "\\seq_reverse",
        "\\seq_length", "\\index_of", "\\seq_concat", "\\empty", "\\singleton", "\\set_union",
        "\\intersect", "\\set_minus", "\\all_fields", "\\infinite_union",
        "\\strictly_than_nothing" };

    /** the style of annotations */
    private final SimpleAttributeSet annotation = new SimpleAttributeSet();

    /* the style of strings */
    // private SimpleAttributeSet string = new SimpleAttributeSet();

    /** default style */
    private final SimpleAttributeSet normal = new SimpleAttributeSet();

    /** the style of keywords */
    private final SimpleAttributeSet keyword = new SimpleAttributeSet();

    /** the style of comments and line comments */
    private final SimpleAttributeSet comment = new SimpleAttributeSet();

    /** the style of JavaDoc */
    private final SimpleAttributeSet javadoc = new SimpleAttributeSet();

    /** the style of JML annotations */
    private final SimpleAttributeSet jml = new SimpleAttributeSet();

    /** the style of JML keywords */
    private final SimpleAttributeSet jmlkeyword = new SimpleAttributeSet();

    /** stores the keywords */
    private final Set<String> keywords = new HashSet<>(KEYWORDS.length);

    /** stores the JML keywords */
    private final Set<String> jmlkeywords = new HashSet<>(JMLKEYWORDS.length);

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

    /**
     * Stores the mode in which the parser currently is.
     */
    private JavaDocument.Mode mode = Mode.NORMAL;

    /**
     * Stores the current comment state of the parser to recognize comments/comment ends.
     */
    private JavaDocument.CommentState state = CommentState.NO;

    /**
     * The settings listener of this document (registered in the static listener list).
     */
    private final transient PropertyChangeListener listener = e -> updateStyles();

    /**
     * Creates a new JavaDocument and sets the syntax highlighting styles (as in eclipse default
     * settings).
     */
    public JavaDocument() {
        updateStyles();
        ColorSettings.getInstance().addPropertyChangeListener(listener);
        // workaround for #1641: typing "enter" key shall insert only "\n", even on Windows
        putProperty(DefaultEditorKit.EndOfLineStringProperty, "\n");

        // fill the keyword hash sets
        keywords.addAll(Arrays.asList(KEYWORDS));
        jmlkeywords.addAll(Arrays.asList(JMLKEYWORDS));
    }

    /**
     * Dispose this object.
     */
    public void dispose() {
        ColorSettings.getInstance().removePropertyChangeListener(listener);
    }

    private void updateStyles() {
        // set the styles
        StyleConstants.setBold(keyword, true);
        StyleConstants.setForeground(keyword, JAVA_KEYWORD_COLOR.get());
        StyleConstants.setForeground(comment, COMMENT_COLOR.get());
        StyleConstants.setForeground(javadoc, JAVADOC_COLOR.get());
        // StyleConstants.setForeground(string, JAVA_STRING_COLOR);
        StyleConstants.setForeground(jml, JML_COLOR.get());
        StyleConstants.setForeground(jmlkeyword, JML_KEYWORD_COLOR.get());
        StyleConstants.setBold(jmlkeyword, true);
    }

    private void checkAt() {
        token += '@';
        if (state == CommentState.COMMENT) { // "/*@"
            state = CommentState.NO;
            mode = Mode.JML;
        } else if (state == CommentState.LINECOMMENT) { // "//@"
            state = CommentState.NO;
            mode = Mode.LINE_JML;
        } else if (mode == Mode.NORMAL && state == CommentState.NO) { // "@"
            mode = Mode.ANNOTATION;
            tokenStart = currentPos;
        } else if (state == CommentState.JML_ANNOTATION
                || state == CommentState.JML_ANNOTATION_LINE) {
            boolean lineComment = state == CommentState.JML_ANNOTATION_LINE;
            state = CommentState.NO;
            String features = token.substring(2); // cut-off '//' or '/*'
            if (isJmlCommentStarter(features)) {
                mode = lineComment ? Mode.LINE_JML : Mode.JML;
            } else {
                mode = lineComment ? Mode.LINE_COMMENT : Mode.COMMENT;
            }
        }
    }


    private void checkSpaceTab(char c) {
        token += c;
        state = CommentState.NO;
    }

    private void checkPlusMinus(char c) {
        if (state == CommentState.LINECOMMENT || state == CommentState.JML_ANNOTATION_LINE) {
            // "//+" or "//-"
            token += c;
            state = CommentState.JML_ANNOTATION_LINE;
        } else if (state == CommentState.COMMENT || state == CommentState.JML_ANNOTATION) {
            // "/*+" or "/*-"
            token += c;
            state = CommentState.JML_ANNOTATION;
        } else {
            token += c;
            state = CommentState.NO;
        }
    }

    private void checkLinefeed() throws BadLocationException {
        state = CommentState.NO;
        if (mode == Mode.LINE_COMMENT) { // "// ... \n"
            insertCommentString(token, tokenStart);
            mode = Mode.NORMAL; // reset
            token = "\n"; // reset token
            tokenStart = currentPos;
        } else if (mode == Mode.LINE_JML) { // "//@ ... \n"
            insertJMLString(token, tokenStart);
            mode = Mode.NORMAL; // reset
            token = "\n"; // reset token
            tokenStart = currentPos;
        } else if (mode == Mode.ANNOTATION) { // "@ ... \n"
            insertAnnotation(token, tokenStart);
            mode = Mode.NORMAL; // reset
            token = "\n"; // reset token
            tokenStart = currentPos;
        } else if (mode == Mode.NORMAL) { // normal mode
            insertNormalString(token, tokenStart);
            token = "\n"; // reset token
            tokenStart = currentPos;
        } else { // modes: JML, Comment, JavaDoc
            token += '\n';
        }
    }

    private void checkStar() throws BadLocationException {
        if (state == CommentState.MAYBE) { // "/*"
            // insert what we have in this line so far
            insertNormalString(token.substring(0, token.length() - 1), tokenStart);
            token = "/*";
            tokenStart = currentPos - 1;
            state = CommentState.COMMENT;
            mode = Mode.COMMENT;
        } else if (state == CommentState.COMMENT) { // "/**"
            // tokenStart should be already set here
            token += '*';
            state = CommentState.MAYBEEND;
            mode = Mode.JAVADOC;
        } else if (mode == Mode.COMMENT // "/* ... *"
                || mode == Mode.JAVADOC // "/*@ ... *"
                || mode == Mode.JML) { // "/** ... *"
            // tokenStart should be already set here
            token += '*';
            state = CommentState.MAYBEEND;
        } else { // multiplication
            token += '*';
            state = CommentState.NO;
        }
    }

    private void checkSlash() throws BadLocationException {
        if (mode == Mode.NORMAL && state == CommentState.NO) { // "/"
            token += '/';
            state = CommentState.MAYBE;
        } else if (state == CommentState.MAYBE) { // "//"
            // insert what we have in this line so far
            insertNormalString(token.substring(0, token.length() - 1), tokenStart);
            token = "//";
            tokenStart = currentPos - 1;
            state = CommentState.LINECOMMENT;
            mode = Mode.LINE_COMMENT;
        } else if (state == CommentState.MAYBEEND) { // "/* ... */"
            token += '/';
            if (mode == Mode.COMMENT) {
                insertCommentString(token, tokenStart);
            } else if (mode == Mode.JAVADOC) {
                if (token.equals("/**/")) { // "/**/" is no JavaDoc
                    insertCommentString(token, tokenStart);
                } else {
                    insertJavadocString(token, tokenStart);
                }
            } else if (mode == Mode.JML) {
                insertJMLString(token, tokenStart);
            }
            state = CommentState.NO;
            mode = Mode.NORMAL;
            token = ""; // reset token
            tokenStart = currentPos + 1;
        } else {
            // not NORMAL_MODE
            token += '/';
        }
    }

    private void checkQuote() { // TODO: separate style for Strings
        state = CommentState.NO;
        token += '"';
    }

    private void checkOther(char c) {
        token += c;

        if (state != CommentState.JML_ANNOTATION && state != CommentState.JML_ANNOTATION_LINE) {
            state = CommentState.NO;
        }
    }

    private void checkDelimiter(char c) {
        token += c;
        state = CommentState.NO;
    }

    private void processChar(char strChar) throws BadLocationException {
        switch (strChar) {
        case ('@') -> checkAt();
        case '\n' -> checkLinefeed();
        // all tabs should have been replaced earlier!
        case '\t', ' ' -> checkSpaceTab(strChar);
        case '*' -> checkStar();
        case '/' -> checkSlash();
        case '"' -> checkQuote();

        // keyword delimiters: +-*/(){}[]%!^~.;?:&|<>="'\n(space)
        case '+', '-' -> checkPlusMinus(strChar);

        // case '*':
        // case '/':
        case '(', ')', '[', ']', '{', '}', '%', '!', '^', '~', '&', '|', '.', ':', ';', '?', '<', '>', '=', '\'' ->
            // case ' ':
            // case '"':
            // case '\'':
            // case '\n':
            checkDelimiter(strChar);
        default -> checkOther(strChar);
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
            if (jmlkeywords.contains(t)) {
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
            if (keywords.contains(t)) {
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
            processChar(str.charAt(strpos));
        }
        // place the internal "cursor" of the document after the inserted String, reset internal
        // state to defaults (fixes problems when editing a document)
        currentPos = endpos;
        tokenStart = endpos;
        token = "";
        mode = Mode.NORMAL;
        state = CommentState.NO;
    }
}
