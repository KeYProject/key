/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.parsing.Location;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * A {@code .key} file may {@code \include} other {@code .key} files. This test ensures that an
 * error
 * inside an <em>included</em> file is reported against that file (its URI, line and column) and not
 * against the including file.
 *
 * @author Claude (improveErrorMessages)
 */
public class IncludeErrorReportingTest {

    /**
     * Writes main.key (including inc.key) and inc.key with the given (broken) content; loads it.
     */
    private Throwable loadWithInclude(String incContent) throws Exception {
        Path dir = Files.createTempDirectory("include");
        Files.writeString(dir.resolve("inc.key"), incContent);
        Path main = dir.resolve("main.key");
        Files.writeString(main, "\\include \"inc.key\";\n\n\\problem { true }\n");
        try {
            KeYEnvironment.load(main);
            fail("expected loading to fail because of the broken include");
            throw new IllegalStateException("unreachable");
        } catch (Throwable t) {
            return t;
        }
    }

    private static Location locationOf(Throwable t) throws Exception {
        Location loc = ExceptionTools.getLocation(t);
        assertNotNull(loc, "a location is expected");
        assertNotNull(loc.getFileUri(), "the location must name a file");
        assertTrue(loc.getFileUri().toString().endsWith("inc.key"),
            "the error must point at the included file inc.key, but was: " + loc.getFileUri());
        return loc;
    }

    @Test
    public void syntaxErrorInIncludeReportsIncludedFile() throws Exception {
        // missing ';' after the declaration of f in inc.key (line 2)
        Throwable t = loadWithInclude("\\functions {\n   int f\n   int g;\n}\n");
        assertTrue(ExceptionTools.getMessage(t).contains("expected"),
            "expected a syntax-error message, but was: " + ExceptionTools.getMessage(t));
        Location loc = locationOf(t);
        assertEquals(2, loc.getPosition().line(),
            "the missing ';' should be reported at the end of line 2 of inc.key");
    }

    @Test
    public void semanticErrorInIncludeReportsIncludedFile() throws Exception {
        // duplicate function declaration in inc.key (second one on line 3)
        Throwable t = loadWithInclude("\\functions {\n   int f;\n   int f;\n}\n");
        assertTrue(ExceptionTools.getMessage(t).contains("Function 'f' is already defined!"),
            "unexpected message: " + ExceptionTools.getMessage(t));
        Location loc = locationOf(t);
        assertEquals(3, loc.getPosition().line(),
            "the duplicate should be reported on line 3 of inc.key");
    }

    @Test
    public void tacletErrorInIncludeReportsIncludedFile() throws Exception {
        // incomplete \find term inside a taclet in inc.key (line 3)
        Throwable t = loadWithInclude(
            "\\rules {\n   r {\n      \\find(0 = )\n      \\replacewith(true)\n   };\n}\n");
        Location loc = locationOf(t);
        assertEquals(3, loc.getPosition().line(),
            "the taclet syntax error should be reported on line 3 of inc.key");
    }
}
