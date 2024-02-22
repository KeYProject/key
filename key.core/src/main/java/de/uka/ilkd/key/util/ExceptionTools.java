/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.net.MalformedURLException;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.parser.proofjava.TokenMgrError;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.NoViableAltException;
import org.antlr.v4.runtime.Vocabulary;
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
    public static String getMessage(Throwable throwable) {
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

    public static String getNiceMessage(InputMismatchException ime) {
        return getNiceMessageInternal(ime.getInputStream(), ime.getOffendingToken(),
            ime.getRecognizer().getVocabulary(), ime.getExpectedTokens());
    }

    public static String getNiceMessage(NoViableAltException ime) {
        return getNiceMessageInternal(ime.getInputStream(), ime.getOffendingToken(),
            ime.getRecognizer().getVocabulary(), ime.getExpectedTokens());
    }

    private static String getNiceMessageInternal(IntStream inputStream,
            org.antlr.v4.runtime.Token offendingToken, Vocabulary vocabulary,
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
        sb.append("Found token which was not expected: ");
        sb.append(vocabulary.getDisplayName(offendingToken.getType()));
        sb.append("\n");
        sb.append("Expected token type(s): ");
        for (var interval : expectedTokens.getIntervals()) {
            for (int i = interval.a; i <= interval.b; i++) {
                sb.append(vocabulary.getDisplayName(i));
                sb.append("\n");
            }
        }

        return sb.toString();
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
    public static Optional<Location> getLocation(@NonNull Throwable exc)
            throws MalformedURLException {
        if (exc instanceof HasLocation) {
            return Optional.ofNullable(((HasLocation) exc).getLocation());
        } else if (exc instanceof ParseException) {
            return Optional.ofNullable(getLocation((ParseException) exc));
        } else if (exc instanceof TokenMgrError) {
            return Optional.ofNullable(getLocation((TokenMgrError) exc));
        } else if (exc instanceof InputMismatchException ime) {
            return Optional.ofNullable(getLocation(ime));
        } else if (exc instanceof NoViableAltException nvae) {
            return Optional.ofNullable(getLocation(nvae));
        }

        if (exc.getCause() != null) {
            return getLocation(exc.getCause());
        }

        return Optional.empty();
    }

    @Nullable
    private static Location getLocation(ParseException exc) {
        // JavaCC has 1-based column numbers
        Token token = exc.currentToken;
        return token == null ? null
                : new Location(null, Position.fromToken(token.next));
    }

    private static Location getLocation(NoViableAltException exc) {
        var token = exc.getOffendingToken();

        return token == null ? null
                : new Location(
                    Paths.get(Paths.get("").toString(), exc.getInputStream().getSourceName())
                            .normalize().toUri(),
                    Position.fromToken(token));
    }

    private static Location getLocation(InputMismatchException exc) {
        var token = exc.getOffendingToken();

        return token == null ? null
                : new Location(
                    Paths.get(Paths.get("").toString(), exc.getInputStream().getSourceName())
                            .normalize().toUri(),
                    Position.fromToken(token));
    }

    private static Location getLocation(TokenMgrError exc) {
        Matcher m = TOKEN_MGR_ERR_PATTERN.matcher(exc.getMessage());
        if (m.find()) {
            int line = Integer.parseInt(m.group(1));
            int col = Integer.parseInt(m.group(2));
            return new Location(null, Position.newOneBased(line, col));
        }
        return null;
    }

}
