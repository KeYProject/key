package de.uka.ilkd.key.gui.sourceview;

import de.uka.ilkd.key.gui.colors.ColorSettings;

import java.awt.Color;
import java.util.HashSet;
import java.util.Set;

import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;

/**
 * This document performs syntax highlighting when strings are inserted.
 * However, only inserting the whole String at once is supported, otherwise the syntax highlighting
 * will be faulty.
 *
 * Note that tab characters have to be replaced by spaces before inserting into the document.
 *
 * @author Wolfram Pfeifer
 */
public class JavaDocument extends DefaultStyledDocument {

    private static final long serialVersionUID = -1856296532743892931L;

    // highlighting colors (same as in HTMLSyntaxHighlighter of SequentView for consistency)

    /** highight color for Java keywords (dark red/violet) */
    private static final ColorSettings.ColorProperty JAVA_KEYWORD_COLOR =
            ColorSettings.define("[java]keyword", "",
            new Color(0x7f0055));

    //private static final Color JAVA_STRING_COLOR = new Color(0x000000);

    /** highight color for comments (dull green) */
    private static final ColorSettings.ColorProperty COMMENT_COLOR =
            ColorSettings.define("[java]comment", "",
                    new Color(0x3f7f5f));

    /** highight color for JavaDoc (dull green) */
    private static final ColorSettings.ColorProperty JAVADOC_COLOR =
            ColorSettings.define("[java]javadoc", "",
                    new Color(0x3f7f5f));

    /** highight color for JML (dark blue) */
    private static final ColorSettings.ColorProperty JML_COLOR =
            ColorSettings.define("[java]jml", "",
                    new Color(0x0000c0));

    /** highight color for JML keywords (blue) */
    private static final ColorSettings.ColorProperty JML_KEYWORD_COLOR =
            ColorSettings.define("[java]jmlKeyword", "",
                    new Color(0x0000f0));

    /**
     * Enum to indicate the current mode (environment) of the parser.
     * Examples are STRING ("..."), COMMENT (&#47;&#42; ... &#42;&#47;),
     * JML (&#47;&#42;&#64; ... &#42;&#47; ), ...
     */
    private enum Mode {
        /** parser is currently inside a String */
        //STRING,                                           // currently not in use
        /** parser is currently inside normal java code */
        NORMAL,
        /** parser is currently inside a keyword */
        KEYWORD,
        /** parser is currently inside a comment (starting with "&#47;&#42;") */
        COMMENT,
        /** parser is currently inside a line comment (starting with "&#47;&#47;") */
        LINE_COMMENT,
        /** parser is currently inside a line JML annotation (starting with "&#47;&#47;&#64;")*/
        LINE_JML,
        /** parser is currently inside JavaDoc (starting with "&#47;&#42;&#42;") */
        JAVADOC,
        /** parser is currently inside an annotation (starting with "&#64;")*/
        ANNOTATION,
        /** parser is currently inside a JML annotation (starting with "&#47;&#42;&#64;") */
        JML,
        /** parser is currently inside a JML keyword */
        JML_KEYWORD;
    }

    /**
     * Enum to indicate the current comment state of the parser.
     * It is used to store which comment relevant chars were just recently encountered.
     */
    private enum CommentState {
        /** no comment char encountered */
        NO,
        /** last processed char was "&#47;" */
        MAYBE,
        /** last processed chars were "&#47;&#42;" */
        COMMENT,
        /** last processed chars were "&#47;&#47;" */
        LNECOMMENT,
        /** last processed char was "&#42;" */
        MAYBEEND;
    }

    /**
     * Regular expression character class for all chars which are delimiters
     * of keywords. \\Q ... \\E is used to escape all chars inside the class.
     */
    private static final String DELIM = "[\\Q .;{}[]\n\r()+-*/%!=<>?:~&|^@'\"\\E]";

    /**
     * Stores the Java keywords which have to be highlighted.
     * The list is taken from
     * <a href="https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html">
     * https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
     * </a>.
     *
     * To add additional keywords, simply add them to the array.
     * Note that the keywords must not contain any of the characters defined by the DELIM regex.
     */
    private static final String[] KEYWORDS = {
        "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char", "class",
        "continue", "default", "do", "double", "else", "enum", "extends", "final", "finally",
        "float", "for", "if", "implements", "import", "instanceof", "int", "interface", "long",
        "native", "new", "package", "private", "protected", "public", "return", "short",
        "static", "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
        "transient", "try", "void", "volatile", "while",
        "true", "false", "null"        // literals
        // "const", "goto" // reserved, but currently not used in Java
    };

    /**
     * Stores the JML keywords which have to be highlighted.
     *
     * To add additional keywords, simply add them to the array.
     * Note that the keywords must not contain any of the characters defined by the DELIM regex.
     */
    private static final String[] JMLKEYWORDS = {
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

    /** the style of annotations */
    private SimpleAttributeSet annotation = new SimpleAttributeSet();

    /** the style of strings */
    //private SimpleAttributeSet string = new SimpleAttributeSet();

    /** default style */
    private SimpleAttributeSet normal = new SimpleAttributeSet();

    /** the style of keywords */
    private SimpleAttributeSet keyword = new SimpleAttributeSet();

    /** the style of comments and line comments */
    private SimpleAttributeSet comment = new SimpleAttributeSet();

    /** the style of JavaDoc */
    private SimpleAttributeSet javadoc = new SimpleAttributeSet();

    /** the style of JML annotations */
    private SimpleAttributeSet jml = new SimpleAttributeSet();

    /** the style of JML keywords */
    private SimpleAttributeSet jmlkeyword = new SimpleAttributeSet();

    /** stores the keywords */
    private Set<String> keywords = new HashSet<String>(KEYWORDS.length);

    /** stores the JML keywords */
    private Set<String> jmlkeywords = new HashSet<String>(JMLKEYWORDS.length);

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
     *  Stores the current comment state of the parser to recognize comments/comment ends.
     */
    private JavaDocument.CommentState state = CommentState.NO;

    /**
     * Creates a new JavaDocument and sets the syntax highlighting styles
     * (as in eclipse default settings).
     */
    public JavaDocument () {
        updateStyles();
        ColorSettings.getInstance().addSettingsListener(e -> updateStyles());

        // fill the keyword hash sets
        for (String k : KEYWORDS) {
            keywords.add(k);
        }

        for (String k : JMLKEYWORDS) {
            jmlkeywords.add(k);
        }
    }

    private void updateStyles() {
        // set the styles
        StyleConstants.setBold(keyword, true);
        StyleConstants.setForeground(keyword, JAVA_KEYWORD_COLOR.get());
        StyleConstants.setForeground(comment, COMMENT_COLOR.get());
        StyleConstants.setForeground(javadoc, JAVADOC_COLOR.get());
        //StyleConstants.setForeground(string, JAVA_STRING_COLOR);
        StyleConstants.setForeground(jml, JML_COLOR.get());
        StyleConstants.setForeground(jmlkeyword, JML_KEYWORD_COLOR.get());
        StyleConstants.setBold(jmlkeyword, true);
    }

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
        } else {                                        // multiplication
            token = token + '*';
            state = CommentState.NO;
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

    private void checkQuote() {                 // TODO: separate style for Strings
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

    private void processChar(String str) throws BadLocationException {
        char strChar = str.charAt(0);

        switch (strChar) {
        case ('@'):
            checkAt();
            break;
        case '\n':  // TODO: different line endings? -> use System.lineSeparator()
            checkLinefeed();
            break;
        //case '\t':  // all tabs should have been replaced earlier!
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
            processChar(Character.toString(str.charAt(strpos)));
        }
        currentPos = offs;
    }
}