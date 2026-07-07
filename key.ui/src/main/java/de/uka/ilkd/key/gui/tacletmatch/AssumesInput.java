/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

/**
 * GUI-independent logic for the "type the {@code \assumes} sequent" editor: how the two typed parts
 * are combined for the parser, where an error offset falls, whether the parsed arity matches, how a
 * parse-failure exception is reduced to a clean message and position, and how the model status maps
 * to an OK/incomplete verdict.
 *
 * <p>
 * Deliberately free of AWT/Swing so it can be unit-tested without a display; the panel keeps only
 * the widget wiring (text areas, highlighting, status colours) and delegates the decisions here.
 */
final class AssumesInput {

    /** the separator inserted between the typed antecedent and succedent before parsing. */
    static final String SEPARATOR = " ==> ";

    private AssumesInput() {}

    /** the single string handed to the sequent parser for the typed antecedent and succedent. */
    static String combined(String ante, String succ) {
        return ante + SEPARATOR + succ;
    }

    /** which part of {@link #combined} an absolute offset falls into. */
    enum Side {
        ANTECEDENT, SEPARATOR, SUCCEDENT
    }

    /** an absolute offset resolved to a {@link Side} and the offset local to that side's text. */
    record Target(Side side, int offset) {
    }

    /**
     * resolves an absolute offset in {@link #combined(String, String)} to the side it belongs to
     * and the offset within that side's own text. Offsets on the boundary count as the antecedent
     * (at its end) or the succedent (at its start); offsets strictly inside the separator are
     * reported as {@link Side#SEPARATOR} and have no place in either text area.
     */
    static Target locate(String ante, int absoluteOffset) {
        int sepStart = ante.length();
        int sepEnd = sepStart + SEPARATOR.length();
        if (absoluteOffset <= sepStart) {
            return new Target(Side.ANTECEDENT, absoluteOffset);
        }
        if (absoluteOffset >= sepEnd) {
            return new Target(Side.SUCCEDENT, absoluteOffset - sepEnd);
        }
        return new Target(Side.SEPARATOR, absoluteOffset - sepStart);
    }

    /**
     * {@code null} if the parsed arity matches the expectation, otherwise a message describing the
     * mismatch.
     */
    static String arityError(int parsedAnte, int parsedSucc, int expectedAnte, int expectedSucc) {
        if (parsedAnte == expectedAnte && parsedSucc == expectedSucc) {
            return null;
        }
        return "expected " + expectedAnte + " antecedent and " + expectedSucc
            + " succedent formula(s), got " + parsedAnte + " and " + parsedSucc;
    }

    /** verdict derived from the dialog model's status string. */
    enum StatusKind {
        OK, INCOMPLETE
    }

    /** the {@link StatusKind} and the text to show for it. */
    record ModelStatus(StatusKind kind, String text) {
    }

    /**
     * classifies the model's status string: a leading "Instantiation is OK" is an {@link
     * StatusKind#OK} verdict carrying the full text, anything else is {@link StatusKind#INCOMPLETE}
     * carrying only its first line.
     */
    static ModelStatus classify(String modelStatus) {
        if (modelStatus != null && modelStatus.startsWith("Instantiation is OK")) {
            return new ModelStatus(StatusKind.OK, modelStatus);
        }
        return new ModelStatus(StatusKind.INCOMPLETE, TmText.firstLine(modelStatus));
    }

    /**
     * a cleaned parse-failure message and the source position it points at (may be {@code null}).
     */
    record SyntaxError(String message, Position position) {
    }

    /**
     * reduces a parse-failure exception chain to a clean, single-line message and (if present) the
     * offending source position. The message drops the noisy " at &lt;pos&gt;" suffix (via {@link
     * BuildingException#getRawMessage()}) and the bare "unknown" placeholder, falling back to a
     * generic "syntax error".
     */
    static SyntaxError extract(Throwable e) {
        String msg = null;
        Position pos = null;
        for (Throwable t = e; t != null; t = t.getCause()) {
            if (msg == null && t instanceof BuildingException be) {
                msg = be.getRawMessage();
            }
            if (pos == null && t instanceof HasLocation hl) {
                Location loc = hl.getLocation();
                if (loc != null && loc.getPosition() != null
                        && !loc.getPosition().equals(Position.UNDEFINED)) {
                    pos = loc.getPosition();
                }
            }
            if (msg == null) {
                msg = t.getMessage();
            }
        }
        if (msg == null || msg.isBlank() || msg.equalsIgnoreCase("unknown")) {
            msg = "syntax error";
        } else {
            msg = humanize(TmText.firstLine(msg));
            if (msg.isBlank()) {
                msg = "syntax error";
            }
        }
        return new SyntaxError(msg, pos);
    }

    /**
     * the various parser phrasings (ANTLR's and KeY's "… expected, but found 'X'"), all of which
     * quote the single offending token.
     */
    private static final Pattern OFFENDING = Pattern.compile(
        "(?:missing \\S+ at|extraneous input|mismatched input|no viable alternative at input|"
            + "token recognition error at:?|but found) '(.*?)'");

    /**
     * turns a raw parser message into a short, plain one. Strips a leading "line L:C" position (the
     * offending spot is highlighted separately) and rephrases the parser's wordings to a simple
     * "unexpected '&lt;token&gt;'". The implicit {@code ==>} separator and end-of-input are never
     * named — each field holds only one side of the sequent, so the parser hitting them just means
     * the formula there is unfinished ("incomplete formula"), not a missing sequent arrow.
     */
    static String humanize(String raw) {
        if (raw == null) {
            return "";
        }
        String m = raw.trim().replaceFirst("^(line\\s+)?\\d+:\\d+:?\\s*", "");
        Matcher tok = OFFENDING.matcher(m);
        if (tok.find()) {
            String t = tok.group(1);
            if ("==>".equals(t) || "<EOF>".equals(t)) {
                return "incomplete formula";
            }
            return "unexpected '" + t + "'";
        }
        return m;
    }
}
