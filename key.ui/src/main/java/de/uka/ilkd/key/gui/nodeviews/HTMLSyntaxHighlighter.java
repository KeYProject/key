/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.lang.ref.WeakReference;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Objects;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.text.html.HTMLDocument;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.util.UnicodeHelper.*;

/**
 * Performs a simple pattern-based syntax highlighting for KeY sequents by adding styled HTML tags.
 * <p>
 *
 * The main method is {@link #process(String, Node)}.
 * <p>
 *
 * NOTE: There should be a more elegant and stable way to achieve this, e.g. by creating a
 * specialized LogicPrinter. However, this is a very involved job to do since all kinds of changes
 * would have to performed to other classes, for instance to maintain a correct position table in
 * the sequent view.
 *
 * @author Dominic Scheurer
 */
public class HTMLSyntaxHighlighter {
    private static final Logger LOGGER = LoggerFactory.getLogger(HTMLSyntaxHighlighter.class);

    // The below two constants are thresholds used to decide whether
    // syntax highlighting for program variables should be realized
    // or not (can be very expensive).
    private static final int NUM_FORMULAE_IN_SEQ_THRESHOLD = 25;
    private static final int NUM_PROGVAR_THRESHOLD = 10;

    ///////////////////////////////////////
    ///////// PROPOSITIONAL LOGIC /////////
    ///////////////////////////////////////

    // NOTE: Spaces in this definition have been added on purpose.
    private final static String[] PROP_LOGIC_KEYWORDS = { "<->", "->", " & ", " | ", "!", "true",
        "false", "" + EQV, "" + IMP, "" + AND, "" + OR, "" + NEG, "" + TOP, "" + BOT };

    private final static String PROP_LOGIC_KEYWORDS_REGEX =
        concat("|", Arrays.asList(PROP_LOGIC_KEYWORDS),
            input -> Pattern.quote(toHTML((String) input)));

    public final static Pattern PROP_LOGIC_KEYWORDS_PATTERN =
        Pattern.compile(concat("(", PROP_LOGIC_KEYWORDS_REGEX, ")"));

    private static final String PROP_LOGIC_KEYWORDS_REPLACEMENT =
        "<span class=\"prop_logic_highlight\">$1</span>";

    ///////////////////////////////////////
    ///////// DYNAMIC LOGIC /////////
    ///////////////////////////////////////

    private final static String[] DYNAMIC_LOGIC_KEYWORDS =
        { "\\forall", "\\exists", "TRUE", "FALSE", "\\if", "\\then", "\\else", "\\sum", "bsum",
            "\\in", "exactInstance", "wellFormed", "measuredByEmpty", "<created>", "<inv>", "\\cup",
            "" + FORALL, "" + EXISTS, "" + IN, "" + EMPTY };

    private final static String DYNAMIC_LOGIC_KEYWORDS_REGEX =
        concat("|", Arrays.asList(DYNAMIC_LOGIC_KEYWORDS), input -> Pattern.quote((String) input));

    public final static Pattern DYNAMIC_LOGIC_KEYWORDS_PATTERN =
        Pattern.compile(concat("(", DYNAMIC_LOGIC_KEYWORDS_REGEX, ")"));

    private static final String DYNAMIC_LOGIC_KEYWORDS_REPLACEMENT =
        "<span class=\"dynamic_logic_highlight\">$1</span>";

    ///////////////////////////////////////
    ///////// JAVA /////////
    ///////////////////////////////////////

    private final static String[] JAVA_KEYWORDS =
        { "if", "else", "for", "do", "while", "return", "break", "switch", "case", "continue",
            "try", "catch", "finally", "assert", "null", "throw", "this", "true", "false", "int",
            "char", "long", "short", "byte", "\\Qmethod&#045;frame\\E", "\\Qloop&#045;scope\\E",
            "boolean",
            "exec", "ccatch", "\\Q\\Return\\E", "\\Q\\Break\\E", "\\Q\\Continue\\E", "final",
            "volatile", "assert", "default" };

    public final static String JAVA_KEYWORDS_REGEX = concat("|", Arrays.asList(JAVA_KEYWORDS));

    // NOTE: \Q(...)\E escapes the String in (...)
    private final static String DELIMITERS_REGEX =
        concat("([\\Q{}[]=*/.!,:<>\\E]|", "\\Q&#040;\\E|", // (
            "\\Q&#041;\\E|", // )
            "\\Q&#059;\\E|", // ;
            "\\Q&#043;\\E|", // +
            "\\Q&#045;\\E|", // -
            "\\Q&nbsp;\\E|", // " "
            "\\Q<br>\\E|", // \n
            "\\Q<br/>\\E|", // \n
            "\\Q&lt;\\E|", // <
            "\\Q&gt;\\E)"); // >

    private final static Pattern JAVA_KEYWORDS_PATTERN =
        Pattern.compile(concat(DELIMITERS_REGEX, "(", JAVA_KEYWORDS_REGEX, ")", DELIMITERS_REGEX));

    private static final Pattern MODALITY_PATTERN =
        Pattern.compile("\\\\(\\[|&lt;).*?\\\\(]|&gt;)");

    private static final String JAVA_KEYWORDS_REPLACEMENT =
        "$1<span class=\"java_highlight\">$2</span>$3";

    private static final String PROGVAR_REPLACEMENT =
        "$1<span class=\"progvar_highlight\">$2</span>$3";

    private static final Pattern SINGLE_LINE_COMMENT_PATTERN = Pattern.compile("(//.*?)<br>");
    private static final String SINGLE_LINE_COMMENT_REPLACEMENT =
        "<span class=\"comment_highlight\">$1</span><br>";

    private static final Pattern SEQUENT_ARROW_PATTERN = Pattern.compile("(==>|⟹)");
    private static final String SEQUENT_ARROW_REPLACEMENT =
        "<span class=\"sequent_arrow_highlight\">$1</span>";


    /**
     * Adds CSS rules to the given document.
     *
     * @param document The {@link HTMLDocument}
     */
    public static void addCSSRulesTo(HTMLDocument document) {
        final String propLogicHighlightRule =
            ".prop_logic_highlight { color: #000000; font-weight: bold; }";
        final String foLogicHighlightRule =
            ".dynamic_logic_highlight { color: #0000C0; font-weight: bold; }";
        final String javaHighlightRule = ".java_highlight { color: #7F0055; font-weight: bold; }";
        final String progVarHighlightRule = ".progvar_highlight { color: #6A3E3E; }";
        final String commentHighlightRule = ".comment_highlight { color: #3F7F5F; }";
        final String sequentArrowHighlightRule =
            ".sequent_arrow_highlight { color: #000000; font-size: 1.7em }";

        document.getStyleSheet().addRule(propLogicHighlightRule);
        document.getStyleSheet().addRule(progVarHighlightRule);
        document.getStyleSheet().addRule(javaHighlightRule);
        document.getStyleSheet().addRule(foLogicHighlightRule);
        document.getStyleSheet().addRule(commentHighlightRule);
        document.getStyleSheet().addRule(sequentArrowHighlightRule);
    }

    /**
     * Computes a String for the given plain text where HTML elements have been escaped and syntax
     * highlighting has been added.
     *
     * @param plainTextString The String to add syntax highlighting to.
     * @param displayedNode The node the sequent of which should be augmented with syntax
     *        highlighting.
     * @return A HTML version of the input String with added syntax highlighting.
     */
    public static String process(String plainTextString, Node displayedNode) {
        try {
            // NOTE: Highlighting program variables is the most expensive operation.
            // There are at least two options to do this:
            // 1. Get all program variables that are registered for a node.
            // Pro: Getting them is fast.
            // Con: There may be a lot of them that are not actually contained
            // in the node's sequent.
            // 2. Find all really existing program variables using a visitor.
            // Pro: No overhead for nonexisting variables.
            // Con: May take quite long to get these variables for big sequents.
            // None of these option works sufficiently well for large sequents.
            // We therefore turn location variable highlighting off in case that
            // there are a lot of registered globals AND the number of formulae
            // in the sequent is big.

            Iterable<? extends IProgramVariable> programVariables;
            final InitConfig initConfig = displayedNode.proof().getInitConfig();

            if (displayedNode.getLocalProgVars().size() < NUM_PROGVAR_THRESHOLD) {
                programVariables = displayedNode.getLocalProgVars();
            } else if (initConfig != null
                    && displayedNode.sequent().size() < NUM_FORMULAE_IN_SEQ_THRESHOLD) {
                programVariables = MergeRuleUtils.getLocationVariablesHashSet(
                    displayedNode.sequent(), initConfig.getServices());
            } else {
                programVariables = new HashSet<ProgramVariable>();
            }

            // We use div-s instead of br-s because this preserves the line
            // breaks in JEditorPane's plain text.
            return concat("<div>", addSyntaxHighlighting(toHTML(plainTextString), programVariables)
                    .replaceAll("<br>", "</div><div>"),
                "</div>");
        } catch (Throwable t) {
            // Syntax highlighting should never break the system;
            // so we catch all throwables. However, a bug should
            // be filed with the stack trace printed here.
            LOGGER.warn("Syntax highlighting failed", t);
            return toHTML(plainTextString);
        }

    }

    /**
     * Adds syntax highlighting to the given HTML String.
     *
     * @param htmlString The HTML String to add syntax highlighting tags to.
     * @param programVariables The program variables to highlight.
     * @return The input String augmented by syntax highlighting tags.
     */
    private static String addSyntaxHighlighting(String htmlString,
            Iterable<? extends IProgramVariable> programVariables) {

        htmlString = PROP_LOGIC_KEYWORDS_PATTERN.matcher(htmlString)
                .replaceAll(PROP_LOGIC_KEYWORDS_REPLACEMENT);

        htmlString = DYNAMIC_LOGIC_KEYWORDS_PATTERN.matcher(htmlString)
                .replaceAll(DYNAMIC_LOGIC_KEYWORDS_REPLACEMENT);

        htmlString =
            SEQUENT_ARROW_PATTERN.matcher(htmlString).replaceAll(SEQUENT_ARROW_REPLACEMENT);

        Matcher modalityMatcher = MODALITY_PATTERN.matcher(htmlString);
        while (modalityMatcher.find()) {
            String modality = modalityMatcher.group();
            modality =
                JAVA_KEYWORDS_PATTERN.matcher(modality).replaceAll(JAVA_KEYWORDS_REPLACEMENT);

            modality = SINGLE_LINE_COMMENT_PATTERN.matcher(modality)
                    .replaceAll(SINGLE_LINE_COMMENT_REPLACEMENT);

            htmlString = htmlString.replace(modalityMatcher.group(), modality);
        }

        StringTransformer progVarTransformer = input -> {
            ProgramVariable progVar = (ProgramVariable) input;
            return Pattern.quote(toHTML(progVar.name().toString()));
        };

        final String concatenatedProgVars = concat("|", programVariables, progVarTransformer);

        if (!concatenatedProgVars.isEmpty()) {
            htmlString = htmlString.replaceAll(
                concat(DELIMITERS_REGEX, "(", concatenatedProgVars, ")", DELIMITERS_REGEX),
                PROGVAR_REPLACEMENT);
        }

        return htmlString;

    }

    /**
     * Shortcut for {@link LogicPrinter#escapeHTML(String, boolean)}.
     *
     * @param plainTextString The String to transform.
     * @return A HTML-compatible version of plainTextString.
     */
    public static String toHTML(String plainTextString) {
        return LogicPrinter.escapeHTML(plainTextString, true);
    }

    /**
     * Concatenates the given String array where the elements are separated by the given delimiter
     * in the result String.
     *
     * @param delim Delimiter for the elements in the array.
     * @param strings Strings to concatenate.
     * @return The concatenated array, elements separated by the given delimiter.
     */
    private static String concat(String delim, Iterable<?> strings) {
        return concat(delim, strings, Object::toString);
    }

    /**
     * Concatenates the given String array where the elements are separated by the given delimiter
     * in the result String.
     *
     * @param delim Delimiter for the elements in the array.
     * @param strings Strings to concatenate.
     * @param strTransformer Transformation applied to the input Strings before the concatenation is
     *        performed.
     * @return The concatenated array, elements separated by the given delimiter.
     */
    private static String concat(String delim, Iterable<?> strings,
            StringTransformer strTransformer) {
        StringBuilder sb = new StringBuilder();
        boolean loopEntered = false;
        for (Object str : strings) {
            sb.append(strTransformer.transform(str));
            sb.append(delim);
            loopEntered = true;
        }
        return loopEntered ? sb.substring(0, sb.length() - delim.length()) : "";
    }

    /**
     * Concatenates the given Strings using a {@link StringBuilder}.
     *
     * @param strings Strings to concatenate.
     * @return The concatenated Strings.
     */
    public static String concat(String... strings) {
        return concat("", Arrays.asList(strings), input -> (String) input);
    }

    /**
     * Simple interface as a replacement for a lambda realizing a String transformation.
     */
    private interface StringTransformer {
        String transform(Object input);
    }

    /**
     * Set of args to the highlighter that produce the same output
     */
    public static final class Args {
        /** The node */
        public final WeakReference<Node> node;
        /** The printed node */
        public final String text;
        /** whether to use html highlighting */
        public final boolean useHtml;

        public Args(Node node, String text, boolean useHtml) {
            this.node = new WeakReference<>(node);
            this.text = text;
            this.useHtml = useHtml;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (o == null || getClass() != o.getClass()) {
                return false;
            }
            Args that = (Args) o;
            return useHtml == that.useHtml && Objects.equals(node.get(), that.node.get())
                    && text.equals(that.text);
        }

        @Override
        public int hashCode() {
            return Objects.hash(node.get(), text, useHtml);
        }

        public String run() {
            var ref = node.get();
            if (useHtml && ref != null) {
                return HTMLSyntaxHighlighter.process(text, ref);
            } else {
                return HTMLSyntaxHighlighter.toHTML(text);
            }
        }
    }
}
