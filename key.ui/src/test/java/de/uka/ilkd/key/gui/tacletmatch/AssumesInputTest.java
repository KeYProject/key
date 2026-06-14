/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link AssumesInput}, the GUI-independent logic of the "type the {@code \assumes}
 * sequent" editor. Parsing itself (which needs a {@link de.uka.ilkd.key.java.Services}) is not
 * exercised here; everything tested is pure and runs headlessly.
 */
public class AssumesInputTest {

    @Test
    public void combined() {
        assertEquals("a ==> b", AssumesInput.combined("a", "b"));
        assertEquals(" ==> ", AssumesInput.combined("", ""));
    }

    @Test
    public void locateAntecedent() {
        // ante = "ab" (length 2), separator " ==> " at [2,7)
        AssumesInput.Target t = AssumesInput.locate("ab", 1);
        assertEquals(AssumesInput.Side.ANTECEDENT, t.side());
        assertEquals(1, t.offset());
    }

    @Test
    public void locateBoundaryEndOfAntecedentIsAntecedent() {
        // an offset exactly at the end of the antecedent stays in the antecedent
        AssumesInput.Target t = AssumesInput.locate("ab", 2);
        assertEquals(AssumesInput.Side.ANTECEDENT, t.side());
        assertEquals(2, t.offset());
    }

    @Test
    public void locateInsideSeparator() {
        // offsets strictly inside " ==> " (here absolute 3..6) belong to neither editor
        AssumesInput.Target t = AssumesInput.locate("ab", 4);
        assertEquals(AssumesInput.Side.SEPARATOR, t.side());
    }

    @Test
    public void locateBoundaryStartOfSuccedentIsSuccedent() {
        // sepEnd = 2 + 5 = 7; offset 7 is the first succedent character
        AssumesInput.Target t = AssumesInput.locate("ab", 7);
        assertEquals(AssumesInput.Side.SUCCEDENT, t.side());
        assertEquals(0, t.offset());
    }

    @Test
    public void locateSuccedentOffsetIsLocal() {
        AssumesInput.Target t = AssumesInput.locate("ab", 9);
        assertEquals(AssumesInput.Side.SUCCEDENT, t.side());
        assertEquals(2, t.offset(), "offset is relative to the start of the succedent text");
    }

    @Test
    public void arityErrorMatch() {
        assertNull(AssumesInput.arityError(1, 2, 1, 2), "matching arity reports no error");
    }

    @Test
    public void arityErrorMismatch() {
        assertEquals("expected 1 antecedent and 1 succedent formula(s), got 2 and 0",
            AssumesInput.arityError(2, 0, 1, 1));
        assertEquals("expected 0 antecedent and 2 succedent formula(s), got 1 and 1",
            AssumesInput.arityError(1, 1, 0, 2));
    }

    @Test
    public void classifyOk() {
        AssumesInput.ModelStatus s =
            AssumesInput.classify("Instantiation is OK and ready to apply");
        assertEquals(AssumesInput.StatusKind.OK, s.kind());
        assertEquals("Instantiation is OK and ready to apply", s.text(),
            "the OK verdict carries the full status text");
    }

    @Test
    public void classifyIncompleteKeepsFirstLine() {
        AssumesInput.ModelStatus s =
            AssumesInput.classify("Rule is not applicable\nsome detail on the next line");
        assertEquals(AssumesInput.StatusKind.INCOMPLETE, s.kind());
        assertEquals("Rule is not applicable", s.text(), "only the first line is kept");
    }

    @Test
    public void classifyNull() {
        AssumesInput.ModelStatus s = AssumesInput.classify(null);
        assertEquals(AssumesInput.StatusKind.INCOMPLETE, s.kind());
        assertEquals("", s.text());
    }

    @Test
    public void extractPlainMessageNoPosition() {
        AssumesInput.SyntaxError err = AssumesInput.extract(new RuntimeException("boom"));
        assertEquals("boom", err.message());
        assertNull(err.position());
    }

    @Test
    public void extractKeepsOnlyFirstLineOfMessage() {
        AssumesInput.SyntaxError err =
            AssumesInput.extract(new RuntimeException("first line\nsecond line"));
        assertEquals("first line", err.message());
    }

    @Test
    public void extractBlankMessageFallsBackToSyntaxError() {
        assertEquals("syntax error", AssumesInput.extract(new RuntimeException("   ")).message());
        assertEquals("syntax error", AssumesInput.extract(new RuntimeException((String) null))
                .message());
    }

    @Test
    public void extractUnknownPlaceholderFallsBackToSyntaxError() {
        assertEquals("syntax error",
            AssumesInput.extract(new RuntimeException("unknown")).message());
        assertEquals("syntax error",
            AssumesInput.extract(new RuntimeException("UNKNOWN")).message(),
            "the 'unknown' placeholder is dropped case-insensitively");
    }

    @Test
    public void extractWalksTheCauseChainForTheMessage() {
        Throwable cause = new IllegalStateException("real cause");
        AssumesInput.SyntaxError err =
            AssumesInput.extract(new RuntimeException((String) null, cause));
        assertEquals("real cause", err.message(),
            "a null top-level message is taken from the cause");
    }

    @Test
    public void extractPrefersRawMessageOfBuildingException() {
        // BuildingException.getMessage() appends " at <pos>"; extract must use the raw message
        BuildingException be =
            new BuildingException((org.antlr.v4.runtime.Token) null, "bad term", null);
        AssumesInput.SyntaxError err = AssumesInput.extract(be);
        assertEquals("bad term", err.message(), "the raw message, not the ' at <pos>' form");
        assertNull(err.position(), "an undefined location yields no position");
    }

    @Test
    public void extractTakesPositionFromHasLocation() {
        Location loc = new Location(null, Position.newOneBased(2, 5));
        AssumesInput.SyntaxError err = AssumesInput.extract(new LocatedException("oops", loc));
        assertEquals("oops", err.message());
        assertNotNull(err.position());
        assertEquals(2, err.position().line());
        assertEquals(5, err.position().column());
    }

    @Test
    public void extractIgnoresUndefinedLocation() {
        AssumesInput.SyntaxError err =
            AssumesInput.extract(new LocatedException("oops", Location.UNDEFINED));
        assertNull(err.position(), "an UNDEFINED position is treated as no position");
    }

    /** a throwable carrying a source location, to exercise the {@link HasLocation} branch. */
    private static final class LocatedException extends RuntimeException implements HasLocation {
        private static final long serialVersionUID = 1L;
        private final Location location;

        LocatedException(String message, Location location) {
            super(message);
            this.location = location;
        }

        @Override
        public Location getLocation() {
            return location;
        }
    }
}
