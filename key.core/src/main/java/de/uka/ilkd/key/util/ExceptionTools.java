package de.uka.ilkd.key.util;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.parser.proofjava.TokenMgrError;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.runtime.RecognitionException;

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
     * Tries to resolve the location (i.e., file name, line, and column) from a parsing exception.
     * Result may be null.
     *
     * @param exc the Throwable to extract the Location from
     * @return the Location stored inside the Throwable or null if no such can be found
     * @throws MalformedURLException if the no URL can be parsed from the String stored inside the
     *         given Throwable can not be successfully converted to a URL and thus no Location can
     *         be created
     */
    public static @Nullable Location getLocation(@Nonnull Throwable exc)
            throws MalformedURLException {
        Location location = null;
        if (exc instanceof HasLocation) {
            return ((HasLocation) exc).getLocation();
        } else if (exc instanceof RecognitionException) {
            location = getLocation((RecognitionException) exc);
        } else if (exc instanceof ParseException) {
            location = getLocation((ParseException) exc);
        } else if (exc instanceof TokenMgrError) {
            location = getLocation((TokenMgrError) exc);
        }

        if (location == null && exc.getCause() != null) {
            location = getLocation(exc.getCause());
        }

        return location;
    }

    @Nullable
    private static Location getLocation(ParseException exc) {
        // JavaCC has 1-based column numbers
        Token token = exc.currentToken;
        return token == null ? null
                : new Location((URL) null, Position.fromToken(token.next));
    }

    private static URL parseFileName(String filename) throws MalformedURLException {
        return filename == null ? null : MiscTools.parseURL(filename);
    }

    @Nullable
    private static Location getLocation(RecognitionException exc) throws MalformedURLException {
        // ANTLR 3 - Recognition Exception.
        if (exc.input != null) {
            // ANTLR has 0-based column numbers
            return new Location(parseFileName(exc.input.getSourceName()),
                Position.fromOneZeroBased(exc.line, exc.charPositionInLine));
        }
        return null;
    }

    private static Location getLocation(TokenMgrError exc) {
        Matcher m = TOKEN_MGR_ERR_PATTERN.matcher(exc.getMessage());
        if (m.find()) {
            int line = Integer.parseInt(m.group(1));
            int col = Integer.parseInt(m.group(2));
            return new Location((URL) null, Position.newOneBased(line, col));
        }
        return null;
    }

}
