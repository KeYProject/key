/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.util.UnicodeHelper;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Pattern-based syntax highlighting for printed sequents; the JavaFX counterpart of
 * {@code de.uka.ilkd.key.gui.nodeviews.HTMLSyntaxHighlighter}. The Swing version inserts styled
 * HTML spans into the printed text; here the same regular expressions produce
 * {@link Highlight} intervals over the <emph>plain</emph> printed string, which
 * {@link SequentViewF#rebuildRuns()} renders as styled {@link javafx.scene.text.Text} runs (no
 * HTML, no AWT).
 * <p>
 * The categories and colors follow the Swing highlighter: bold propositional operators, bold
 * dark-blue dynamic-logic keywords, bold Java keywords and comments/JML inside modality blocks,
 * program variables and the sequent arrow in the accent color. Where the Swing patterns overlap,
 * the pattern applied <emph>last</emph> wins (innermost HTML span), which is mirrored here by an
 * explicit priority: program variables &gt; JML &gt; comments &gt; Java &gt; arrow &gt;
 * dynamic logic &gt; propositional logic.
 * <p>
 * Deviations from the Swing version (noted for parity review): the keywords are
 * {@link Pattern#quote}-wrapped. The Swing regexes join the raw strings, so {@code \forall}
 * compiled as a form-feed escape and {@code $inv} as an end-of-input anchor and never matched
 * anything; the quoted variants match the intended literals. The Swing arrow highlight enlarges
 * the arrow to 1.7em, which would break the character grid of the position table, so the arrow is
 * only colored and bolded here. Like in Swing, all throwables are caught: highlighting must never
 * break the view.
 */
final class SequentSyntaxHighlighterF {

    private static final Logger LOGGER = LoggerFactory.getLogger(SequentSyntaxHighlighterF.class);

    /** Style category of a highlight interval. */
    enum Kind {
        PROP, DYN, JAVA, PROGVAR, COMMENT, JML, ARROW
    }

    /** A highlighted range {@code [start, end)} of the printed sequent text. */
    record Highlight(int start, int end, Kind kind) {
    }

    /** Swing thresholds: program-variable highlighting is skipped for large sequents. */
    private static final int NUM_FORMULAE_IN_SEQ_THRESHOLD = 25;
    private static final int NUM_PROGVAR_THRESHOLD = 10;

    /** Delimiters around Java keywords and program variables (plain-text form of the Swing set). */
    private static final String DELIMITERS = "[{}\\[\\]=*/.!,:<>();+\\-\\s]";

    private static final Pattern PROP_PATTERN = Pattern.compile(alternatives(List.of("<->", "->",
        " & ", " | ", "!", "true", "false", "" + UnicodeHelper.EQV, "" + UnicodeHelper.IMP,
        "" + UnicodeHelper.AND, "" + UnicodeHelper.OR, "" + UnicodeHelper.NEG,
        "" + UnicodeHelper.TOP, "" + UnicodeHelper.BOT)));

    private static final Pattern DYN_PATTERN = Pattern
            .compile(alternatives(List.of("\\forall", "\\exists", "TRUE", "FALSE", "\\if",
                "\\then", "\\else", "\\sum", "bsum", "\\in", "instance", "exactInstance",
                "wellFormed", "measuredByEmpty", "<created>", "$inv", "\\cup",
                "" + UnicodeHelper.FORALL, "" + UnicodeHelper.EXISTS, "" + UnicodeHelper.IN,
                "" + UnicodeHelper.EMPTY)));

    private static final Pattern ARROW_PATTERN =
        Pattern.compile(Pattern.quote("==>") + "|" + Pattern.quote("\u27F9"));

    private static final Pattern JAVA_PATTERN =
        Pattern.compile("(?<=" + DELIMITERS + ")(" + alternatives(Arrays.asList("if", "else",
            "for", "do", "while", "return", "break", "switch", "case", "continue", "try", "catch",
            "finally", "assert", "null", "throw", "this", "true", "false", "int", "char", "long",
            "short", "byte", "method-frame", "loop-scope", "boolean", "exec", "ccatch",
            "\\Return", "\\Break", "\\Continue", "final", "volatile", "default")) + ")(?="
            + DELIMITERS + ")");

    /** Modality blocks {@code \[...\]} and {@code \<...\>}, across line breaks like in Swing. */
    private static final Pattern MODALITY_PATTERN =
        Pattern.compile("\\\\[\\[<].*?\\\\[\\]>]", Pattern.DOTALL);

    private static final Pattern COMMENT_PATTERN = Pattern.compile("//[^@].*?(?=\\n|$)");

    private static final Pattern JML_PATTERN = Pattern.compile("//@.*?(?=\\n|$)");

    private SequentSyntaxHighlighterF() {
    }

    /**
     * Computes the highlight intervals of the printed sequent text.
     *
     * @param text the printed sequent, may be {@code null}
     * @param node the displayed node, source of the program variables; may be {@code null}
     * @return the highlights in no particular order; empty on any error
     */
    static List<Highlight> highlight(String text, Node node) {
        List<Highlight> result = new ArrayList<>();
        if (text == null || text.isEmpty() || node == null) {
            return result;
        }
        try {
            findAll(result, text, PROP_PATTERN, Kind.PROP);
            findAll(result, text, DYN_PATTERN, Kind.DYN);
            findAll(result, text, ARROW_PATTERN, Kind.ARROW);
            // Java keywords, comments and JML only inside modality blocks, like in Swing; the
            // patterns run on the block substring so the block borders act as delimiters
            Matcher modality = MODALITY_PATTERN.matcher(text);
            while (modality.find()) {
                String block = text.substring(modality.start(), modality.end());
                addMatches(result, block, JAVA_PATTERN, Kind.JAVA, modality.start());
                addMatches(result, block, COMMENT_PATTERN, Kind.COMMENT, modality.start());
                addMatches(result, block, JML_PATTERN, Kind.JML, modality.start());
            }
            // program variables, with the Swing performance guards for large sequents
            StringBuilder alternation = new StringBuilder();
            for (IProgramVariable progvar : collectProgramVariables(node)) {
                if (!alternation.isEmpty()) {
                    alternation.append('|');
                }
                alternation.append(Pattern.quote(progvar.name().toString()));
            }
            if (!alternation.isEmpty()) {
                Pattern progvarPattern = Pattern.compile(
                    "(?<=" + DELIMITERS + ")(" + alternation + ")(?=" + DELIMITERS + ")");
                findAll(result, text, progvarPattern, Kind.PROGVAR);
            }
        } catch (Throwable t) {
            // Syntax highlighting should never break the view; the Swing highlighter catches all
            // throwables for the same reason.
            LOGGER.warn("Syntax highlighting failed", t);
            return List.of();
        }
        return result;
    }

    /**
     * @return the program variables to highlight, with the Swing guards: the node's local program
     *         variables if few, otherwise the sequent's location variables if the sequent is
     *         small, otherwise none
     */
    private static Iterable<? extends IProgramVariable> collectProgramVariables(Node node) {
        if (node.getLocalProgVars().size() < NUM_PROGVAR_THRESHOLD) {
            return node.getLocalProgVars();
        }
        InitConfig initConfig = node.proof().getInitConfig();
        if (initConfig != null && node.sequent().size() < NUM_FORMULAE_IN_SEQ_THRESHOLD) {
            return MergeRuleUtils.getLocationVariablesHashSet(node.sequent(),
                initConfig.getServices());
        }
        return List.of();
    }

    private static void findAll(List<Highlight> result, String text, Pattern pattern, Kind kind) {
        addMatches(result, text, pattern, kind, 0);
    }

    private static void addMatches(List<Highlight> result, String text, Pattern pattern,
            Kind kind, int offset) {
        Matcher matcher = pattern.matcher(text);
        while (matcher.find()) {
            if (matcher.end() > matcher.start()) {
                result.add(new Highlight(offset + matcher.start(), offset + matcher.end(), kind));
            } else {
                matcher.region(matcher.start() + 1, text.length());
            }
        }
    }

    /** @return the alternatives joined with {@code |}, each {@link Pattern#quote}-wrapped */
    private static String alternatives(List<String> keywords) {
        StringBuilder sb = new StringBuilder();
        for (String keyword : keywords) {
            if (!sb.isEmpty()) {
                sb.append('|');
            }
            sb.append(Pattern.quote(keyword));
        }
        return sb.toString();
    }

    /**
     * @return the CSS style class of the category, defined in the key-light/key-dark themes
     */
    static String styleClass(Kind kind) {
        return switch (kind) {
            case PROP -> "sequent-hl-prop";
            case DYN -> "sequent-hl-dyn";
            case JAVA -> "sequent-hl-java";
            case PROGVAR -> "sequent-hl-progvar";
            case COMMENT -> "sequent-hl-comment";
            case JML -> "sequent-hl-jml";
            case ARROW -> "sequent-hl-arrow";
        };
    }

    /**
     * @return the rendering priority of the category; lower wins where intervals overlap. The
     *         order mirrors the Swing HTML nesting (the last applied span is innermost and wins):
     *         program variables &gt; JML &gt; comments &gt; Java &gt; arrow &gt; dynamic logic
     *         &gt; propositional logic.
     */
    static int priority(Kind kind) {
        return switch (kind) {
            case PROP -> 7;
            case DYN -> 6;
            case ARROW -> 5;
            case JAVA -> 4;
            case COMMENT -> 3;
            case JML -> 2;
            case PROGVAR -> 1;
        };
    }
}
