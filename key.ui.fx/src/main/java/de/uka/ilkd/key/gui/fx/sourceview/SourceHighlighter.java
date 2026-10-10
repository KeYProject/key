/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.sourceview;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.fxmisc.richtext.model.StyleSpans;
import org.fxmisc.richtext.model.StyleSpansBuilder;

/**
 * Minimal Java/JML syntax highlighter for the first JavaFX source view (milestone M2, read-only
 * version). It is a small subset of the Swing original
 * {@code de.uka.ilkd.key.gui.sourceview.JavaJMLEditorLexer}: the Swing lexer is a character-wise
 * state machine with modes for normal text, block/line comments, JavaDoc, JML annotations and
 * Java annotations; here the same categories are recognized by a single left-to-right regex pass
 * (alternation order encodes the priority, e.g. {@code /*@} before {@code /*}) plus a second pass
 * over annotation regions for a trimmed JML keyword set.
 * <p>
 * The result is a flat {@link StyleSpans} value covering the entire text; segments carry style
 * classes (see the {@code source-*} constants) which are colored by the theme stylesheets
 * ({@code key-light.css} / {@code key-dark.css}), mirroring how the Swing lexer's token
 * attributes map onto theme colors.
 * <p>
 * Deliberately not ported (deferred): JML annotation markers with feature lists ({@code /*+@}),
 * JavaDoc distinct from comments, number literals, and the incremental re-parsing (the Swing
 * document re-parses on edits; this view is read-only).
 */
public final class SourceHighlighter {

    /** Style class of plain (unmatched) text segments; themes give it the regular text color. */
    public static final String CLASS_PLAIN = "source-text";

    /** Style class of Java keywords. */
    public static final String CLASS_KEYWORD = "source-keyword";

    /** Style class of block and line comments (JavaDoc is folded into this category). */
    public static final String CLASS_COMMENT = "source-comment";

    /** Style class of string and character literals. */
    public static final String CLASS_STRING = "source-string";

    /**
     * Style class of JML annotations ({@code /*@ ... *}{@code /}, {@code //@}) and Java annotations
     * ({@code @Word}).
     */
    public static final String CLASS_ANNOTATION = "source-annotation";

    /**
     * Style class of JML keywords inside annotation regions (applied in addition to
     * {@link #CLASS_ANNOTATION}).
     */
    public static final String CLASS_JML_KEYWORD = "source-jml-keyword";

    /**
     * Style class of placeholder texts (e.g. "No source loaded") rendered by {@link SourceViewF}.
     */
    public static final String CLASS_PLACEHOLDER = "source-placeholder";

    /**
     * The Java keywords of the Swing lexer, reused unchanged from
     * {@code de.uka.ilkd.key.gui.sourceview.JavaJMLEditorLexer.KEYWORDS} (module {@code key.ui}).
     */
    private static final String[] JAVA_KEYWORDS = { "abstract", "assert", "boolean", "break",
        "byte", "case", "catch", "char", "class", "continue", "default", "do", "double", "else",
        "enum", "extends", "final", "finally", "float", "for", "if", "implements", "import",
        "instanceof", "int", "interface", "long", "native", "new", "package", "private",
        "protected", "public", "return", "short", "static", "strictfp", "super", "switch",
        "synchronized", "this", "throw", "throws", "transient", "try", "void", "volatile",
        "while", "true", "false", "null" };

    /**
     * Trimmed subset of the JML keywords of {@code JavaJMLEditorLexer.JMLKEYWORDS} (the Swing list
     * has more than 200 entries; this keeps the common specification clauses and expressions).
     * Applied only inside annotation regions, so it cannot clash with Java identifiers.
     */
    private static final String[] JML_KEYWORDS = {
        // clause keywords
        "requires", "ensures", "assignable", "assignable_free", "modifiable", "modifiable_free",
        "modifies", "accessible", "decreases", "diverges", "loop_invariant", "measured_by",
        "maintaining", "signals", "signals_only", "unreachable", "when",
        // behavior/invariant-like keywords
        "normal_behavior", "normal_behaviour", "exceptional_behavior", "exceptional_behaviour",
        "behavior", "behaviour", "also", "axiom", "invariant", "initially", "constraint",
        "represents", "for_example", "implies_that", "hence_by",
        // modifiers
        "ghost", "model", "pure", "helper", "nullable", "non_null", "spec_public",
        "spec_protected", "instance", "peer", "code", "extract", "two_state",
        // special JML expressions (backslash forms; Pattern.quote escapes them safely)
        "\\old", "\\result", "\\forall", "\\exists", "\\fresh", "\\at", "\\reach", "\\seq",
        "\\seq_contains", "\\bigint", "\\real", "\\locset", "\\TYPE", "\\everything",
        "\\nothing", "\\not_specified", "\\same", "\\type", "\\typeof", "\\invariant_for",
        "\\working_space", "\\lockset", "\\duration", "\\index", "\\min", "\\max", "\\sum",
        "\\num_of", "\\only_assigned", "\\not_assigned", "\\not_modified" };

    /**
     * Alternation order matters: at each position the first matching alternative wins. Each
     * alternative is wrapped in exactly one capturing group (nested groups are non-capturing),
     * so the group index identifies the token category.
     */
    private static final Pattern TOKEN_PATTERN = Pattern
            .compile(String.join("|",
                // 1: JML block annotation /*@ ... @*/ (lazy: stops at the first "*"+"/")
                "(/\\*@[\\s\\S]*?\\*/)",
                // 2: block comment / JavaDoc /* ... */
                "(/\\*[\\s\\S]*?\\*/)",
                // 3: single-line JML annotation //@ ... (before plain //)
                "(//@[^\n]*)",
                // 4: line comment
                "(//[^\n]*)",
                // 5: string literal (no newline)
                "(\"(?:\\\\.|[^\"\\\\\n])*\")",
                // 6: character literal
                "('(?:\\\\.|[^'\\\\\n])*')",
                // 7: Java annotation @Name.dotted
                "(@[A-Za-z_$][A-Za-z0-9_$.]*)",
                // 8: Java keyword
                "\\b((?:" + String.join("|", JAVA_KEYWORDS) + "))\\b"));

    /** Number of capturing groups in {@link #TOKEN_PATTERN}. */
    private static final int GROUP_COUNT = 8;

    /** Style class per group index of {@link #TOKEN_PATTERN} (index 0 is unused). */
    private static final String[] CLASS_BY_GROUP = { null,
        CLASS_ANNOTATION, CLASS_COMMENT, CLASS_ANNOTATION, CLASS_COMMENT, CLASS_STRING,
        CLASS_STRING, CLASS_ANNOTATION, CLASS_KEYWORD };

    /** Groups that are JML regions and therefore receive the JML keyword overlay. */
    private static final boolean[] JML_REGION_BY_GROUP = { false, true, false, true, false, false,
        false, false, false };

    /** JML keyword pattern, used on annotation region texts only. */
    private static final Pattern JML_KEYWORD_PATTERN = Pattern.compile(
        "(?<![\\w$])(?:" + Arrays.stream(JML_KEYWORDS).map(Pattern::quote)
                .collect(Collectors.joining("|"))
            + ")(?![\\w$])");

    private static final List<String> PLAIN_STYLES = List.of(CLASS_PLAIN);
    private static final List<String> ANNOTATION_STYLES = List.of(CLASS_ANNOTATION);
    private static final List<String> ANNOTATION_JML_STYLES =
        List.of(CLASS_ANNOTATION, CLASS_JML_KEYWORD);

    private SourceHighlighter() {
    }

    /**
     * Tokenizes the given text into style spans covering the whole text. Run this off the
     * JavaFX-critical path (e.g. on a loader thread) and apply the spans on the FX thread with
     * {@code setStyleSpans(0, spans)}.
     *
     * @param text the text to highlight, may be empty
     * @return the spans together with the per-category token counts (see {@link Result})
     */
    public static Result highlight(String text) {
        if (text == null || text.isEmpty()) {
            return Result.EMPTY;
        }
        List<Span> spans = new ArrayList<>();
        int keywords = 0;
        int comments = 0;
        int strings = 0;
        int annotations = 0;
        int jmlKeywords = 0;
        int pos = 0;
        Matcher matcher = TOKEN_PATTERN.matcher(text);
        while (matcher.find()) {
            if (matcher.start() > pos) {
                spans.add(new Span(pos, matcher.start(), PLAIN_STYLES));
            }
            int group = matchedGroup(matcher);
            String token = matcher.group();
            if (JML_REGION_BY_GROUP[group]) {
                // JML region: split at JML keywords and stack the second style class on them
                int from = matcher.start();
                Matcher jmlMatcher = JML_KEYWORD_PATTERN.matcher(token);
                int jpos = 0;
                while (jmlMatcher.find()) {
                    if (jmlMatcher.start() > jpos) {
                        spans.add(new Span(from + jpos, from + jmlMatcher.start(),
                            ANNOTATION_STYLES));
                    }
                    spans.add(new Span(from + jmlMatcher.start(), from + jmlMatcher.end(),
                        ANNOTATION_JML_STYLES));
                    jmlKeywords++;
                    jpos = jmlMatcher.end();
                }
                if (jpos < token.length()) {
                    spans.add(new Span(from + jpos, matcher.end(), ANNOTATION_STYLES));
                }
            } else {
                spans.add(new Span(matcher.start(), matcher.end(), List.of(CLASS_BY_GROUP[group])));
            }
            switch (group) {
                case 1, 3, 7 -> annotations++;
                case 2, 4 -> comments++;
                case 5, 6 -> strings++;
                case 8 -> keywords++;
                default -> {
                }
            }
            pos = matcher.end();
        }
        if (pos < text.length()) {
            spans.add(new Span(pos, text.length(), PLAIN_STYLES));
        }
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();
        for (Span span : spans) {
            builder.add(span.classes(), span.to() - span.from());
        }
        int total = keywords + comments + strings + annotations + jmlKeywords;
        return new Result(text.length(), keywords, comments, strings, annotations, jmlKeywords,
            total, builder.create());
    }

    /**
     * Builds the single placeholder span for an explanatory text (e.g. "No source loaded").
     *
     * @param text the placeholder text, must not be empty
     * @return spans styling the whole text with {@link #CLASS_PLACEHOLDER}
     */
    public static StyleSpans<Collection<String>> placeholderSpans(String text) {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();
        builder.add(List.of(CLASS_PLACEHOLDER), text.length());
        return builder.create();
    }

    /**
     * @return the first capturing group of the given match (all alternatives are groups)
     */
    private static int matchedGroup(Matcher matcher) {
        for (int group = 1; group <= GROUP_COUNT; group++) {
            if (matcher.group(group) != null) {
                return group;
            }
        }
        throw new AssertionError("Token without a matching group");
    }

    /**
     * One highlighted region of the text; the class list is the style of the region.
     */
    private record Span(int from, int to, List<String> classes) {
    }

    /**
     * The outcome of one highlighting run: the spans for the whole text plus the token counts per
     * category. Used by {@link SourceViewF#verifySourceView()} for the self-test report.
     *
     * @param length length of the highlighted text
     * @param keywords number of Java keyword tokens
     * @param comments number of comment tokens
     * @param strings number of string/char literal tokens
     * @param annotations number of annotation tokens (JML blocks, //@ lines, @Words)
     * @param jmlKeywords number of JML keyword tokens inside annotation regions
     * @param total sum of all token counts
     * @param spans the style spans covering the whole text ({@code null} only for
     *        {@link #EMPTY})
     */
    public record Result(int length, int keywords, int comments, int strings, int annotations,
            int jmlKeywords, int total, StyleSpans<Collection<String>> spans) {

        /** The empty result (no text, no tokens, no spans). */
        public static final Result EMPTY =
            new Result(0, 0, 0, 0, 0, 0, 0, null);
    }
}
