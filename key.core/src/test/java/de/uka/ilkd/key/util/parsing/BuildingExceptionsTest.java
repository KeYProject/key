/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.util.List;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the improved error reporting of {@link BuildingExceptions} and
 * {@link ConvertException}: the location of the first issue must be exposed (it used to be lost)
 * and the message must mention every reported issue with its position.
 *
 * @author Claude (improveErrorMessages)
 */
class BuildingExceptionsTest {

    @Test
    void singleIssueMessageAndLocation() {
        var located = new BuildingIssue("something went wrong", null, false,
            Position.newOneBased(12, 7), "file:///tmp/test.key");
        var ex = new BuildingExceptions(List.of(located));

        // the message must contain the actual reason and not just a vague header
        assertTrue(ex.getMessage().contains("something went wrong"),
            "message should contain the reason, but was: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("file:///tmp/test.key"),
            "message should mention the source, but was: " + ex.getMessage());
        assertFalse(ex.getMessage().startsWith("Multiple errors"),
            "a single issue should not be reported as 'Multiple errors'");

        // The location used to be lost entirely (BuildingExceptions was not HasLocation).
        Location loc = ex.getLocation();
        assertNotNull(loc);
        assertEquals(12, loc.getPosition().line());
        assertEquals(7, loc.getPosition().column());
        assertTrue(loc.fileUri().toString().endsWith("/tmp/test.key"),
            "unexpected file uri: " + loc.fileUri());

        // ExceptionTools must also be able to extract that location now.
        assertDoesNotThrow(() -> {
            Location viaTools = ExceptionTools.getLocation(ex);
            assertNotNull(viaTools);
            assertEquals(12, viaTools.getPosition().line());
        });
    }

    @Test
    void multipleIssuesAreCounted() {
        var i1 = new BuildingIssue("first", null, false, Position.newOneBased(1, 1), "a.key");
        var i2 = new BuildingIssue("second", null, false, Position.newOneBased(2, 2), "a.key");
        var ex = new BuildingExceptions(List.of(i1, i2));
        assertTrue(ex.getMessage().contains("2 errors occurred"),
            "message should count the issues, but was: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("first") && ex.getMessage().contains("second"));
    }

    @Test
    void convertExceptionWithoutLocationHasNoNoise() {
        var ex = new ConvertException("plain message");
        // Previously this appended a useless "[<unknown>:??]" location suffix.
        assertEquals("plain message", ex.getMessage());
    }
}
