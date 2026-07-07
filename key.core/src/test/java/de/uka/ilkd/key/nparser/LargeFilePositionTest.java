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
 * Ensures that, for a large input file, the reported error position stays at (or very close to)
 * the actual error and does not drift far away - a regression guard for the SLL/LL parsing that
 * historically could report a syntax error at the start of the file.
 *
 * @author Claude (improveErrorMessages)
 */
public class LargeFilePositionTest {

    @Test
    public void errorPositionStaysCloseInLargeFile() throws Exception {
        StringBuilder sb = new StringBuilder("\\functions {\n");
        int errorLine = -1;
        for (int i = 0; i < 400; i++) {
            sb.append("  int f").append(i).append(";\n");
        }
        // The offending declaration is missing its ';'.
        errorLine = 2 + 400; // 1 line for "\functions {" + 400 declarations -> this is line 402
        sb.append("  int boom\n");
        for (int i = 0; i < 400; i++) {
            sb.append("  int g").append(i).append(";\n");
        }
        sb.append("}\n\\problem { true }\n");

        Path big = Files.createTempFile("largePos", ".key");
        Files.writeString(big, sb.toString());
        try {
            KeYEnvironment.load(big);
            fail("expected a parse error");
        } catch (Throwable t) {
            Location loc = ExceptionTools.getLocation(t);
            assertNotNull(loc, "a location is expected");
            int reported = loc.getPosition().line();
            // The error must be reported right around line 402, definitely not near the top.
            assertTrue(Math.abs(reported - errorLine) <= 1,
                "reported line " + reported + " should be close to the actual error line "
                    + errorLine);
        } finally {
            Files.deleteIfExists(big);
        }
    }
}
