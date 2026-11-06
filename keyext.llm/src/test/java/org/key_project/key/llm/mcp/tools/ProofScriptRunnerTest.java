/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import de.uka.ilkd.key.scripts.ScriptBlock;
import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Headless tests for the unified goal targeting of the proof-script tools: {@code parseGoal}, the
 * {@code select number:<n>} prefix and the {@code onAll} wrapper. These build proof-script ASTs
 * only; executing them needs a live main window (covered by the KeY core scripts machinery).
 */
class ProofScriptRunnerTest {

    @Test
    void parseGoalDefaultIsBranch() {
        assertEquals(new ProofScriptRunner.Branch(), ProofScriptRunner.parseGoal(null));
        assertEquals(new ProofScriptRunner.Branch(), ProofScriptRunner.parseGoal(""));
        assertEquals(new ProofScriptRunner.Branch(), ProofScriptRunner.parseGoal("branch"));
    }

    @Test
    void parseGoalAll() {
        assertEquals(new ProofScriptRunner.All(), ProofScriptRunner.parseGoal("all"));
    }

    @Test
    void parseGoalIndex() {
        assertEquals(new ProofScriptRunner.Index(0), ProofScriptRunner.parseGoal("0"));
        assertEquals(new ProofScriptRunner.Index(3), ProofScriptRunner.parseGoal(" 3 "));
        assertEquals(new ProofScriptRunner.Index(-1), ProofScriptRunner.parseGoal("-1"));
    }

    @Test
    void parseGoalRejectsUnknownValue() {
        assertThrows(IllegalArgumentException.class,
            () -> ProofScriptRunner.parseGoal("left"));
        assertThrows(IllegalArgumentException.class,
            () -> ProofScriptRunner.parseGoal("0.5"));
    }

    @Test
    void selectGoalEmitsSelectCommandWithNumber() {
        var select = ProofScriptRunner.selectGoal(2);
        assertEquals("select", select.commandName());
        assertEquals(java.util.Map.of("number", 2), select.namedArgs());
        assertEquals(List.of(), select.positionalArgs());
    }

    @Test
    void onAllWrapsTheCommandInAScriptBlock() {
        var inner = new ScriptCommandAst("oss", java.util.Map.of(), List.of());
        var wrapper = ProofScriptRunner.onAll(inner);
        assertEquals("onAll", wrapper.commandName());
        assertEquals(1, wrapper.positionalArgs().size());
        assertEquals(java.util.Map.of(), wrapper.namedArgs());
        var block = assertInstanceOf(ScriptBlock.class, wrapper.positionalArgs().getFirst());
        assertEquals(List.of(inner), block.commands());
    }

    @Test
    void targetBranchPassesTheCommandThrough() {
        var command = new ScriptCommandAst("auto", java.util.Map.of(), List.of());
        assertEquals(List.of(command),
            ProofScriptRunner.target(new ProofScriptRunner.Branch(), command));
    }

    @Test
    void targetIndexPrefixesASelect() {
        var command = new ScriptCommandAst("auto", java.util.Map.of(), List.of());
        var commands = ProofScriptRunner.target(new ProofScriptRunner.Index(1), command);
        assertEquals(2, commands.size());
        assertEquals("select", commands.get(0).commandName());
        assertEquals(java.util.Map.of("number", 1), commands.get(0).namedArgs());
        assertEquals(command, commands.get(1));
    }

    @Test
    void targetAllWrapsInOnAll() {
        var command = new ScriptCommandAst("macro", java.util.Map.of(), List.of("symbex"));
        var commands = ProofScriptRunner.target(new ProofScriptRunner.All(), command);
        assertEquals(1, commands.size());
        assertEquals("onAll", commands.get(0).commandName());
    }
}
