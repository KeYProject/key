/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.net.MalformedURLException;
import java.util.Optional;
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
    public static Optional<Location> getLocation(@Nonnull Throwable exc)
            throws MalformedURLException {
        if (exc instanceof HasLocation) {
            return Optional.ofNullable(((HasLocation) exc).getLocation());
        } else if (exc instanceof ParseException) {
            return Optional.ofNullable(getLocation((ParseException) exc));
        } else if (exc instanceof TokenMgrError) {
            return Optional.ofNullable(getLocation((TokenMgrError) exc));
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
