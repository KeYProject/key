/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.tools.SubagentTools;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the per-session {@link SubagentLog}: bounded FIFO storage, sequence numbers that survive
 * pruning, and the {@code get_subagent_logs} tool registration + rendering.
 */
class SubagentLogTest {

    private static SubagentLog.SubagentRun run(long started, int durationMs, String role,
            String task,
            SubagentLog.Status status, String... tools) {
        return new SubagentLog.SubagentRun(0L, role, "sequential", started, durationMs,
            List.of(new SubagentLog.SubagentTask(task, status, tools.length, List.of(tools),
                "outcome of " + task)));
    }

    @Test
    void addAssignsSequenceNumbersAndKeepsOrder() {
        var log = new SubagentLog();
        assertEquals(0, log.latestSeq());
        log.add(run(1, 10, "goal-solver", "close goal 2", SubagentLog.Status.OK,
            "get_proof_context", "tryclose"));
        log.add(run(2, 20, "file-explorer", "list files", SubagentLog.Status.OK, "list_files"));
        assertEquals(2, log.size());
        assertEquals(2, log.latestSeq());
        // after(seq) returns the appended runs oldest first
        var appended = log.after(0);
        assertEquals(2, appended.size());
        assertEquals(1, appended.get(0).seq());
        assertEquals(2, appended.get(1).seq());
        assertTrue(log.after(2).isEmpty());
        // newest first snapshot
        assertEquals(2, log.snapshot(10).get(0).seq());
    }

    @Test
    void capacityTrimsOldestButSequenceNumbersStayUnique() {
        var log = new SubagentLog(3);
        for (int i = 1; i <= 5; i++) {
            log.add(run(i, 10, "echo-role", "task " + i, SubagentLog.Status.OK));
        }
        assertEquals(3, log.size());
        assertEquals(5, log.latestSeq());
        var newest = log.snapshot(10);
        assertEquals(List.of(5L, 4L, 3L),
            newest.stream().map(SubagentLog.SubagentRun::seq).toList());
        // pruning never reuses sequence numbers: after(2) still identifies the last three runs
        var since = log.after(2);
        assertEquals(List.of(3L, 4L, 5L),
            since.stream().map(SubagentLog.SubagentRun::seq).toList());
    }

    @Test
    void clearEmptiesTheLog() {
        var log = new SubagentLog();
        log.add(run(1, 10, "echo-role", "x", SubagentLog.Status.OK));
        log.clear();
        assertEquals(0, log.size());
        assertEquals(0, log.latestSeq());
        assertTrue(log.after(0).isEmpty());
        assertTrue(log.snapshot(10).isEmpty());
    }

    @Test
    void getSubagentLogsToolIsRegisteredReadOnly() {
        var tools = new KeYAgentTools().getTools();
        var tool = tools.stream()
                .filter(t -> t.function().name().equals(KeYAgentTools.TOOL_GET_SUBAGENT_LOGS))
                .findFirst()
                .orElseThrow(() -> new AssertionError("get_subagent_logs is not registered"));
        assertEquals(Tool.ApprovalRequirement.AUTO, tool.defaultApproval(),
            "the log is read-only and must not require approval");
    }

    @Test
    void renderSubagentLogListsRunsAndTasks() {
        var log = new SubagentLog();
        log.add(run(1, 500, "goal-solver", "close goal 2", SubagentLog.Status.OK,
            "get_proof_context", "tryclose"));
        log.add(run(2, 250, "file-explorer", "list files", SubagentLog.Status.OK, "list_files"));

        var text = SubagentTools.renderSubagentLog(log, 10, null);
        assertTrue(text.contains("newest first"));
        assertTrue(text.contains("goal-solver"));
        assertTrue(text.contains("file-explorer"));
        assertTrue(text.contains("OK"));
        assertTrue(text.contains("2 round(s)"));
        assertTrue(text.contains("called: get_proof_context, tryclose"),
            "expected the called tools, got:\n" + text);

        var filtered = SubagentTools.renderSubagentLog(log, 10, "file-explorer");
        assertTrue(filtered.contains("task \"list files\""), filtered);
        assertFalse(filtered.contains("goal-solver"), "role filter must hide other roles");
        assertTrue(SubagentTools.renderSubagentLog(log, 10, "rule-designer")
                .contains(
                    "No sub-agent runs recorded for this session with role 'rule-designer'."));
        assertTrue(SubagentTools.renderSubagentLog(new SubagentLog(), 10, null)
                .contains("No sub-agent runs recorded for this session."));
    }
}
