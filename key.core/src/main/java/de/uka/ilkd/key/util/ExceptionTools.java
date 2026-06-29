/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.net.MalformedURLException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.loader.JavaBuildingExceptions;
import de.uka.ilkd.key.java.loader.JavaBuildingIssue;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;
import org.key_project.util.parsing.SourceNames;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.IntervalSet;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


/**
 * Various utility methods related to exceptions.
 *
 * @author bruns
 * @since 2.4.0
 */
public final class ExceptionTools {

    /**
     * This reg. exp. pattern is used to extract the line and column
     * information from a TokenMgrErr that does not store it in separate
     * fields
     */
    public static final Pattern TOKEN_MGR_ERR_PATTERN =
        Pattern.compile("^Lexical error at line (\\d+), column (\\d+)\\.");

    private ExceptionTools() {
    }

    /**
     * Get the throwable's message. This will return a nicer error message for
     * certain ANTLR exceptions.
     *
     * @param throwable a throwable
     * @return message for the exception
     */
    public static String getMessage(@Nullable Throwable throwable) {
        if (throwable == null) {
            return "";
        } else if (throwable instanceof ParseCancellationException
                || throwable instanceof ProblemLoaderException) {
            return getMessage(throwable.getCause());
        } else if (throwable instanceof InputMismatchException ime) {
            return getNiceMessage(ime);
        } else if (throwable instanceof NoViableAltException nvae) {
            return getNiceMessage(nvae);
        } else {
            return throwable.getMessage();
        }
    }

    /**
     * Human-readable names for punctuation tokens. The keys are the display names ANTLR uses for
     * literal tokens (i.e. the literal in single quotes, like {@code "';'"}). They allow us to
     * present "';' (semicolon) expected" instead of the bare and easily-overlooked "';'".
     */
    private static final Map<String, String> PUNCTUATION_NAMES = Map.ofEntries(
        Map.entry("';'", "semicolon"),
        Map.entry("','", "comma"),
        Map.entry("'.'", "dot"),
        Map.entry("':'", "colon"),
        Map.entry("'('", "opening parenthesis"),
        Map.entry("')'", "closing parenthesis"),
        Map.entry("'{'", "opening brace"),
        Map.entry("'}'", "closing brace"),
        Map.entry("'['", "opening bracket"),
        Map.entry("']'", "closing bracket"),
        Map.entry("'='", "equality sign"),
        Map.entry("'->'", "arrow"),
        Map.entry("'::'", "double colon"),
        Map.entry("'@'", "at sign"));

    /**
     * Extracts all individual error messages with their source locations from a throwable. This is
     * the non-GUI counterpart of the extraction the {@code IssueDialog} performs: it digs into the
     * exceptions that bundle several issues ({@link BuildingExceptions}, {@link
     * JavaBuildingExceptions}) so that each problem (with its own position) is reported, instead of
     * collapsing everything into one generic wrapper message such as "Failed to parse file".
     * <p>
     * The result is suitable for both the GUI and the command line; consumers can render the
     * {@link Location} as they see fit (a source preview with an underline in the GUI, a caret line
     * on the console, ...).
     *
     * @param throwable the throwable to analyse (must not be null)
     * @return a non-empty, position-sorted list of the contained problems
     */
    public static @NonNull List<PositionedString> getMessages(@NonNull Throwable throwable) {
        List<PositionedString> result = new ArrayList<>();
        // Search the cause chain for an exception that bundles several located issues.
        for (Throwable e = throwable; e != null; e = e.getCause()) {
            if (e instanceof ProblemLoaderException ple && !ple.getSubExceptions().isEmpty()) {
                // e.g. a partial proof replay: report every rule application that failed, led by
                // the summary, instead of only the first.
                result.add(new PositionedString(ple.getMessage(), safeLocation(ple)));
                for (Throwable sub : ple.getSubExceptions()) {
                    result.add(new PositionedString(subErrorText(sub), safeLocation(sub)));
                }
                break;
            }
            if (e instanceof SyntaxErrorReporter.ParserException pe && pe.getErrors().size() > 1) {
                // several syntax errors collected from one file: report each with its own location
                for (SyntaxErrorReporter.SyntaxError se : pe.getErrors()) {
                    result.add(new PositionedString(se.getMessage(), se.getLocation()));
                }
                break;
            }
            if (e instanceof BuildingExceptions be) {
                for (BuildingIssue issue : be.getErrors()) {
                    result.add(issue.asPositionedString());
                }
                break;
            }
            if (e instanceof JavaBuildingExceptions je) {
                for (JavaBuildingIssue issue : je.getIssues()) {
                    result.add(new PositionedString(issue.getMessage(),
                        new Location(issue.getPath(), issue.getPosition())));
                }
                break;
            }
            if (e instanceof BuildingException be) {
                // use the raw message: the location is carried separately, so the position would
                // otherwise be printed twice
                result.add(new PositionedString(be.getRawMessage(), safeLocation(be)));
                break;
            }
        }
        if (result.isEmpty()) {
            // Generic case: a single message. getMessage() already unwraps the common wrappers and
            // produces the friendly text for ANTLR exceptions.
            result.add(new PositionedString(getMessage(throwable), safeLocation(throwable)));
        }
        result.sort((a, b) -> a.getLocation().compareTo(b.getLocation()));
        return result;
    }

    private static Location safeLocation(Throwable t) {
        try {
            Location loc = getLocation(t);
            return loc != null ? loc : Location.UNDEFINED;
        } catch (Exception e) {
            return Location.UNDEFINED;
        }
    }

    /**
     * Message for a bundled sub-problem. Prefers the exception's own message (which, for the
     * replay errors, carries the contextual "Line .., goal .., rule .." text); only when it has
     * none do we fall back to {@link #getMessage} (which would otherwise unwrap a
     * {@link ProblemLoaderException} to its cause and drop that context).
     */
    private static String subErrorText(Throwable sub) {
        String own = sub.getMessage();
        return (own != null && !own.isBlank()) ? own : getMessage(sub);
    }

    public static String getNiceMessage(InputMismatchException ime) {
        return getNiceMessageInternal(ime.getInputStream(), ime.getOffendingToken(),
            ime.getRecognizer().getVocabulary(), ime.getExpectedTokens());
    }

    public static String getNiceMessage(NoViableAltException ime) {
        return getNiceMessageInternal(ime.getInputStream(), ime.getOffendingToken(),
            ime.getRecognizer().getVocabulary(), ime.getExpectedTokens());
    }

    private static String getNiceMessageInternal(IntStream inputStream,
            Token offendingToken, Vocabulary vocabulary,
            IntervalSet expectedTokens) {
        StringBuilder sb = new StringBuilder();
        sb.append("Syntax error in input file ");
        var inFile = new File(inputStream.getSourceName());
        sb.append(inFile.getName());
        sb.append("\n");
        sb.append("Line: ");
        sb.append(offendingToken.getLine());
        sb.append(" Column: ");
        sb.append(offendingToken.getCharPositionInLine() + 1);
        sb.append("\n");
        sb.append(describeSyntaxError(vocabulary, offendingToken, expectedTokens));
        return sb.toString();
    }

    /**
     * Produces a concise, human-readable description of an ANTLR syntax error from the offending
     * token and the set of tokens that would have been acceptable at that position.
     * <p>
     * Examples of the produced text:
     * <ul>
     * <li>{@code "';' (semicolon) expected, but found '}'"}</li>
     * <li>{@code "one of ')' (closing parenthesis), ',' (comma) expected, but found 'int'"}</li>
     * <li>{@code "unexpected end of file"} (when no specific token can be expected)</li>
     * </ul>
     *
     * @param vocabulary the parser vocabulary used to resolve token names
     * @param offendingToken the token actually found (may be the EOF token)
     * @param expectedTokens the tokens that would have been valid here (may be empty)
     * @return a one-line, user-friendly description of the syntax error
     */
    public static String describeSyntaxError(Vocabulary vocabulary,
            @Nullable Token offendingToken, @Nullable IntervalSet expectedTokens) {
        String found = describeFound(offendingToken);
        if (expectedTokens == null || expectedTokens.isNil()) {
            return "unexpected " + found;
        }
        return describeExpected(vocabulary, expectedTokens) + " expected, but found " + found;
    }

    private static String describeFound(@Nullable Token offendingToken) {
        if (offendingToken == null || offendingToken.getType() == Token.EOF) {
            return "end of file";
        }
        String text = offendingToken.getText();
        if (text == null || text.isEmpty()) {
            return "end of file";
        }
        return "'" + text + "'";
    }

    private static String describeExpected(Vocabulary vocabulary, IntervalSet expectedTokens) {
        java.util.List<String> names = new java.util.ArrayList<>();
        for (var interval : expectedTokens.getIntervals()) {
            for (int i = interval.a; i <= interval.b; i++) {
                names.add(friendlyTokenName(vocabulary, i));
            }
        }
        if (names.isEmpty()) {
            return "different input";
        }
        if (names.size() == 1) {
            return names.get(0);
        }
        // Keep the listing short and readable; do not dump dozens of alternatives.
        final int limit = 6;
        if (names.size() > limit) {
            return "one of " + String.join(", ", names.subList(0, limit)) + ", ...";
        }
        return "one of " + String.join(", ", names);
    }

    /**
     * Resolves a token type to a readable name, expanding well-known punctuation tokens with their
     * spoken name (e.g. {@code "';' (semicolon)"}).
     */
    private static String friendlyTokenName(Vocabulary vocabulary, int tokenType) {
        if (tokenType == Token.EOF) {
            return "end of file";
        }
        String display = vocabulary.getDisplayName(tokenType);
        String spoken = PUNCTUATION_NAMES.get(display);
        if (spoken != null) {
            return display + " (" + spoken + ")";
        }
        return display;
    }


    /**
     * Tries to resolve the location (i.e., file name, line, and column) from a parsing exception.
     * Result may be null.
     *
     * @param exc the Throwable to extract the Location from
     * @return the Location stored inside the Throwable or null if no such can be found
     * @throws MalformedURLException if the no URL can be parsed from the String stored inside the
     *         given Throwable can not be successfully converted to a URL and thus no Location can
     *         be created
     */
    public static @Nullable Location getLocation(@NonNull Throwable exc)
            throws MalformedURLException {
        if (exc instanceof HasLocation) {
            return ((HasLocation) exc).getLocation();
        }

        if (exc instanceof InputMismatchException ime) {
            return reportLocationFor(ime);
        }

        // NoViableAltException is the other common ANTLR parse error (e.g. an unexpected token at
        // the start of a term). It also carries the offending token; without this branch such
        // errors had a message but no location, so the GUI/console could not show the source.
        if (exc instanceof NoViableAltException nvae) {
            return Location.fromToken(nvae.getOffendingToken());
        }

        if (exc.getCause() != null) {
            return getLocation(exc.getCause());
        }

        return null;
    }

    /**
     * Tokens that "close" or "terminate" a construct. When one of these is the only acceptable
     * token, the parser has hit the symbol that comes <em>after</em> the place where the missing
     * token belongs, so the more helpful location is the end of the preceding construct.
     */
    private static final java.util.Set<String> CLOSING_TOKENS =
        java.util.Set.of("';'", "')'", "']'", "'}'");

    /**
     * Chooses the location to report for an {@link InputMismatchException}.
     * <p>
     * By default this is the offending (unexpected) token. However, when the only acceptable token
     * is a closing/terminating one (e.g. a missing {@code ';'} or {@code ')'}), the unexpected
     * token is the one <em>following</em> the place where the missing token belongs. In that case
     * the position just <em>after</em> the preceding token is more helpful, as it points right at
     * the spot where the missing token should be inserted (the squiggly then sits at the gap right
     * after the construct that was not terminated/closed, e.g. where the ')' belongs).
     *
     * @param ime the input mismatch exception
     * @return the location to report
     */
    private static @Nullable Location reportLocationFor(InputMismatchException ime) {
        Token offending = ime.getOffendingToken();
        // Single-error path: only redirect to the insertion point when the closing token is the
        // ONLY expected one (the precise SLL prediction yields such tight expected sets).
        Position ip = insertionPointFor(ime, true);
        if (ip == null) {
            return Location.fromToken(offending);
        }
        return new Location(SourceNames.getURIFromTokenSource(offending.getTokenSource()), ip);
    }

    /**
     * The insertion-point position for a missing closing/terminating token: one past the preceding
     * token, i.e. the spot where the missing {@code ';'}/{@code ')'}/... belongs (rather than the
     * next, unexpected token). Returns {@code null} when the heuristic does not apply.
     *
     * @param ime the input mismatch
     * @param onlyClosing if {@code true}, fire only when a closing token is the <em>only</em>
     *        expected token (precise single-error path); if {@code false}, fire when a closing
     *        token
     *        is <em>among</em> the expected ones (multi-error recovery, where LL prediction yields
     *        a
     *        broader expected set so the strict check would never match)
     * @return the 1-based insertion-point position, or {@code null}
     */
    public static @Nullable Position insertionPointFor(InputMismatchException ime,
            boolean onlyClosing) {
        Token offending = ime.getOffendingToken();
        boolean applies =
            onlyClosing ? expectsOnlyClosingToken(ime) : expectedContainsClosingToken(ime);
        if (!applies || offending == null
                || !(ime.getInputStream() instanceof TokenStream ts)) {
            return null;
        }
        // Search backwards for the previous token on the default channel (skip
        // whitespace/comments).
        for (int i = offending.getTokenIndex() - 1; i >= 0; i--) {
            Token prev = ts.get(i);
            if (prev.getChannel() == Token.DEFAULT_CHANNEL && prev.getType() != Token.EOF) {
                String text = prev.getText();
                int len = text == null ? 1 : Math.max(1, text.length());
                // 1-based column of the insertion point: one past the last character of the
                // preceding token (where the missing closing token belongs)
                return Position.newOneBased(prev.getLine(), prev.getCharPositionInLine() + len + 1);
            }
        }
        return null;
    }

    /**
     * @return true iff the only token expected at the error position is a closing/terminating token
     *         (see {@link #CLOSING_TOKENS}).
     */
    private static boolean expectsOnlyClosingToken(InputMismatchException ime) {
        IntervalSet expected = ime.getExpectedTokens();
        if (expected == null || expected.size() != 1) {
            return false;
        }
        Vocabulary vocabulary = ime.getRecognizer().getVocabulary();
        return CLOSING_TOKENS.contains(vocabulary.getDisplayName(expected.getMinElement()));
    }

    /**
     * @return true iff a closing/terminating token (see {@link #CLOSING_TOKENS}) is among the
     *         expected tokens at the error position.
     */
    private static boolean expectedContainsClosingToken(InputMismatchException ime) {
        IntervalSet expected = ime.getExpectedTokens();
        if (expected == null || expected.isNil()) {
            return false;
        }
        Vocabulary vocabulary = ime.getRecognizer().getVocabulary();
        for (int type : expected.toList()) {
            if (CLOSING_TOKENS.contains(vocabulary.getDisplayName(type))) {
                return true;
            }
        }
        return false;
    }
}
