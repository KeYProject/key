/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for issue #3409: a generic sort must never occur in a concrete {@code \problem}. The check
 * is applied at the user-input boundary ({@code KeYUserProblemFile.readProblem}); generic sorts
 * remain legal inside taclets.
 */
class GenericSortInProblemTest {

    private static void load(String dir) throws Exception {
        Path p = Paths.get(GenericSortInProblemTest.class.getResource(dir).toURI());
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(p, null, null, null);
        env.dispose();
    }

    /** A constant of generic sort used in the problem term must be rejected. */
    @Test
    void genericSortInProblemIsRejected() {
        ProblemLoaderException ex = assertThrows(ProblemLoaderException.class,
            () -> load("genericProblem/genericConst.key"));
        String msg = collectMessages(ex);
        assertTrue(msg.contains("generic sort") && msg.contains("'S'"),
            "expected a clear 'generic sort S' rejection, got: " + msg);
        assertTrue(msg.contains("\\problem") || msg.contains("problem"),
            "message should mention the problem context, got: " + msg);
    }

    /**
     * A generic sort that is merely declared but does not appear in the problem term must still
     * load (only the leak into the sequent is illegal).
     */
    @Test
    void genericSortDeclaredButUnusedStillLoads() {
        assertDoesNotThrow(() -> load("genericProblem/genericDeclaredOnly.key"));
    }

    private static String collectMessages(Throwable t) {
        StringBuilder sb = new StringBuilder();
        for (Throwable c = t; c != null && c != c.getCause(); c = c.getCause()) {
            sb.append(c.getMessage()).append(" | ");
        }
        return sb.toString();
    }
}
