/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm.mcp;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Headless tests for the parameter mapping of the proof-manipulation tools {@code tryclose} and
 * {@code auto}. The execution itself needs a live main window and is covered by the KeY core
 * proof-script machinery.
 */
class KeYAgentToolsCommandTest {

    @Test
    void trycloseDefaultsToCurrentBranch() {
        var cmd = KeYAgentTools.tryCloseCommand(null, null, false);
        assertEquals("tryclose", cmd.commandName());
        assertEquals(java.util.List.of("branch"), cmd.positionalArgs());
        assertEquals(java.util.Map.of(), cmd.namedArgs());
    }

    @Test
    void trycloseExplicitBranchWithSteps() {
        var cmd = KeYAgentTools.tryCloseCommand("branch", 100, false);
        assertEquals(java.util.List.of("branch"), cmd.positionalArgs());
        assertEquals(java.util.Map.of("steps", 100), cmd.namedArgs());
    }

    @Test
    void trycloseAllGoalsWithoutPositional() {
        var cmd = KeYAgentTools.tryCloseCommand("all", null, false);
        assertEquals(java.util.List.of(), cmd.positionalArgs());
        assertEquals(java.util.Map.of(), cmd.namedArgs());
    }

    @Test
    void trycloseByIndexWithAssertClosed() {
        var cmd = KeYAgentTools.tryCloseCommand("2", 50, true);
        assertEquals(java.util.List.of("2"), cmd.positionalArgs());
        assertEquals(java.util.Map.of("steps", 50, "assertClosed", true), cmd.namedArgs());
    }

    @Test
    void trycloseRejectsUnknownBranchValue() {
        assertThrows(IllegalArgumentException.class,
            () -> KeYAgentTools.tryCloseCommand("left", null, false));
    }

    @Test
    void autoWithoutParameters() {
        var cmd = KeYAgentTools.autoCommand(null, false);
        assertEquals("auto", cmd.commandName());
        assertEquals(java.util.List.of(), cmd.positionalArgs());
        assertEquals(java.util.Map.of(), cmd.namedArgs());
    }

    @Test
    void autoWithSteps() {
        var cmd = KeYAgentTools.autoCommand(200, false);
        assertEquals(java.util.Map.of("steps", 200), cmd.namedArgs());
    }

    @Test
    void autoAllGoals() {
        var cmd = KeYAgentTools.autoCommand(100, true);
        assertEquals(java.util.Map.of("steps", 100, "all", true), cmd.namedArgs());
    }
}
