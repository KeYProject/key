package de.uka.ilkd.key.gui.nodeviews;

import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.JEditorPane;
import javax.swing.text.html.HTMLDocument;

import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * Performs a simple pattern-based syntax highlighting for KeY sequents by
 * adding styled HTML tags.
 * <p>
 * 
 * The main method is {@link #process(String, Node)}.
 * <p>
 * 
 * NOTE: There should be a more elegant and stable way to achieve this, e.g. by
 * creating a specialized LogicPrinter. However, this is a very involved job to
 * do since all kinds of changes would have to performed to other classes, for
 * instance to maintain a correct position table in the sequent view.
 *
 * @author Dominic Scheurer
 */
public class HTMLSyntaxHighlighter {

    // The below two constants are thresholds used to decide whether
    // syntax highlighting for program variables should be realized
    // or not (can be very expensive).
    private static final int NUM_FORMULAE_IN_SEQ_THRESHOLD = 25;
    private static final int NUM_PROGVAR_THRESHOLD = 10;

    // NOTE: Spaces in this definition have been added on purpose.
    private final static String[] PROP_LOGIC_KEYWORDS = { "<->", "->", "&",
            " | ", "!", "true", "false", };
    
    private final static String[] DYNAMIC_LOGIC_KEYWORDS = { "\\forall",
            "\\exists", "TRUE", "FALSE", "\\if", "\\then", "\\else", "\\sum",
            "bsum", "\\in", "exactInstance", "wellFormed", "measuredByEmpty",
            "method-frame", "<created>", "<inv>", "\\cup" };

    private final static String[] JAVA_KEYWORDS = { "if", "else", "for", "do",
            "while", "return", "break", "switch", "case", "continue", "try",
            "catch", "finally", "assert", "null", "throw", "this", "true",
            "false", "int", "char", "long", "short", "boolean" };

    /**
     * Creates a new {@link HTMLSyntaxHighlighter} for this HTMLDocument.
     *
     * @param document
     *            The {@link HTMLDocument} of the parent {@link JEditorPane}.
     *            Used to add CSS rules.
     */
    public HTMLSyntaxHighlighter(HTMLDocument document) {
        final String propLogicHighlightRule =
                ".prop_logic_highlight { color: #000000; font-weight: bold; }";
        final String foLogicHighlightRule =
                ".dynamic_logic_highlight { color: #0000C0; font-weight: bold; }";
        final String javaHighlightRule =
                ".java_highlight { color: #7F0055; font-weight: bold; }";
        final String progVarHighlightRule =
                ".progvar_highlight { color: #6A3E3E; }";

        document.getStyleSheet().addRule(propLogicHighlightRule);
        document.getStyleSheet().addRule(progVarHighlightRule);
        document.getStyleSheet().addRule(javaHighlightRule);
        document.getStyleSheet().addRule(foLogicHighlightRule);
    }

    /**
     * Computes a String for the given plain text where HTML elements have been
     * escaped and syntax highlighting has been added.
     *
     * @param plainTextString
     *            The String to add syntax highlighting to.
     * @param displayedNode
     *            The node the sequent of which should be augmented with syntax
     *            highlighting.
     * @return A HTML version of the input String with added syntax
     *         highlighting.
     */
    public String process(String plainTextString, Node displayedNode) {
        
        // NOTE: Highlighting program variables is the most expensive operation.
        // There are at least to options to do this:
        // 1. Get all program variables that are registered for a node.
        //    Pro: Getting them is fast.
        //    Con: There may be a lot of them that are not actually contained
        //         in the node's sequent.
        // 2. Find all really existing program variables using a visitor.
        //    Pro: No overhead for nonexisting variables.
        //    Con: May take quite long to get these variables for big sequents.
        // None of these option works sufficiently well for large sequents.
        // We therefore turn location variable highlighting off in case that
        // there are a lot of registered globals AND the number of formulae
        // in the sequent is big.
        
        Iterable<? extends ProgramVariable> programVariables;
        
        if (displayedNode.getGlobalProgVars().size() < NUM_PROGVAR_THRESHOLD) {
            programVariables = displayedNode.getGlobalProgVars();
        }
        else if (displayedNode.sequent().size() < NUM_FORMULAE_IN_SEQ_THRESHOLD) {
            programVariables = JoinRuleUtils
                    .getLocationVariablesHashSet(displayedNode.sequent(),
                            displayedNode.proof().getServices());
        }
        else {
            programVariables = new HashSet<ProgramVariable>();
        }

        // We use div-s instead of br-s because this preserves the line
        // breaks in JEditorPane's plain text.
        return "<div>"
                + addSyntaxHighlighting(toHTML(plainTextString),
                        programVariables).replaceAll("<br>", "</div><div>")
                + "</div>";

    }

    /**
     * Adds syntax highlighting to the given HTML String.
     * 
     * @param htmlString
     *            The HTML String to add syntax highlighting tags to.
     * @param programVariables
     *            The program variables to highlight.
     * @return The input String augmented by syntax highlighting tags.
     */
    private String addSyntaxHighlighting(String htmlString,
            Iterable<? extends ProgramVariable> programVariables) {

        // NOTE: \Q(...)\E escapes the String in (...)

        final String delimitersRegex = "([\\Q{}[]=*/.!,:<>\\E]|"
                        + "\\Q&#040;\\E|" // (
                        + "\\Q&#041;\\E|" // )
                        + "\\Q&#059;\\E|" // ;
                        + "\\Q&#043;\\E|" // +
                        + "\\Q&#045;\\E|" // -
                        + "\\Q&nbsp;\\E|" // " "
                        + "\\Q<br>\\E|"   // \n
                        + "\\Q<br/>\\E|"  // \n
                        + "\\Q&lt;\\E|"   // <
                        + "\\Q&gt;\\E)";  // >

        for (String keyword : PROP_LOGIC_KEYWORDS) {
            keyword = toHTML(keyword);
            htmlString =
                    htmlString.replace(keyword,
                            "<span class=\"prop_logic_highlight\">" + keyword
                                    + "</span>");
        }

        for (String keyword : DYNAMIC_LOGIC_KEYWORDS) {
            keyword = toHTML(keyword);
            htmlString =
                    htmlString.replace(keyword,
                            "<span class=\"dynamic_logic_highlight\">" + keyword
                                    + "</span>");
        }

        Matcher modalityMatcher =
                Pattern.compile("\\\\(\\[|&lt;).*?\\\\(\\]|&gt;)").matcher(
                        htmlString);
        while (modalityMatcher.find()) {
            String modality = modalityMatcher.group();
            for (String keyword : JAVA_KEYWORDS) {
                modality =
                        modality.replaceAll(delimitersRegex + keyword
                                + delimitersRegex,
                                "$1<span class=\"java_highlight\">" + keyword
                                        + "</span>$2");
            }
            
            htmlString = htmlString.replace(modalityMatcher.group(), modality);
        }

        for (ProgramVariable progVar : programVariables) {
            String name = toHTML(progVar.name().toString());
            htmlString =
                    htmlString.replaceAll(
                            delimitersRegex + Pattern.quote(name)
                                    + delimitersRegex,
                            "$1<span class=\"progvar_highlight\">" + name
                                    + "</span>$2");
        }

        return htmlString;

    }

    /**
     * Shortcut for {@link LogicPrinter#escapeHTML(String, boolean)}.
     *
     * @param plainTextString
     *            The String to transform.
     * @return A HTML-compatible version of plainTextString.
     */
    private String toHTML(String plainTextString) {
        return LogicPrinter.escapeHTML(plainTextString, true);
    }

}
