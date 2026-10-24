/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import org.key_project.key.llm.AgentLoopTest.MockCompletions;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the user-initiated backgrounding of running tool calls: {@code requestBackground()} parks
 * the loop with {@link AgentResult.PausedForBackground}, the running call (which keeps executing on
 * the {@link ToolDispatcher} pool) delivers its output through the session's {@link TurnQueue} and
 * {@code submitBackgroundOutput} resumes the parked turn. While parked, the unfinished round must
 * not be committed to the context (no dangling {@code tool_calls} for other turns built from it).
 */
class BackgroundAgentLoopTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setMaxToolRounds(8);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.setToolsDisabled(new java.util.TreeSet<>());
        LlmSettings.INSTANCE.getBackgroundToolsEnabled().clear();
        LlmSettings.INSTANCE.getBackgroundToolsDisabled().clear();
        LlmSettings.INSTANCE.setAgentCanUseSkills(false);
        TestMcpToolProvider.reset();
        session = new LlmSession("https://example.invalid", "token", "model");
    }

    @Test
    void backgroundedCallParksTheTurnAndResumesWithItsOutput() throws Exception {
        LlmSettings.INSTANCE.getBackgroundToolsEnabled().add(TestMcpToolProvider.ECHO);
        TestMcpToolProvider.ECHO_DELAY_MS = 600;

        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":1}")), ""));
        mock.thenRespond(MockCompletions.text("done after background"));
        mock.thenRespond(MockCompletions.text("unused"));

        var loop = new AgentLoop(session, mock);
        var beginResult = new CompletableFuture<AgentResult>();
        var thread = new Thread(
            () -> beginResult.complete(loop.begin("go", null, null, null)), "test-begin");
        thread.setDaemon(true);
        thread.start();

        // let the tool start running, then move it into the background
        Thread.sleep(150);
        loop.requestBackground();

        assertInstanceOf(AgentResult.PausedForBackground.class,
            beginResult.get(10, TimeUnit.SECONDS));
        var paused = (AgentResult.PausedForBackground) beginResult.join();
        assertEquals(TestMcpToolProvider.ECHO, paused.toolName());
        assertEquals(1, session.getBackgroundJobs().size(),
            "the background job must be tracked in the registry");

        // the unfinished round is staged, not committed: no dangling tool_calls in the context
        assertTrue(session.getContext().getMessages().stream()
            .noneMatch(m -> "assistant".equals(m.role()) && m.toolCalls() != null),
            "the parked round must not be committed to the context");

        // wait for the running call to finish; its output lands in the session's queue while the
        // registry still tracks the job (the scheduler removes it when it picks up the output)
        var output = waitForToolOutput(paused.jobId());
        assertTrue(output.content().contains("echo:"), output.content());
        assertEquals(1, session.getBackgroundJobs().size(), "job is tracked until consumed");
        var job = session.getBackgroundJobs().take(paused.jobId());
        assertEquals(paused.jobId(), job.jobId());
        assertEquals(0, session.getBackgroundJobs().size());
        session.getTurnQueue().poll(); // consume the delivered output entry

        var resumed = loop.submitBackgroundOutput(paused.jobId(), output.content());
        assertInstanceOf(AgentResult.Done.class, resumed);
        assertEquals("done after background", ((AgentResult.Done) resumed).content());

        // the resolved round is now committed (assistant tool_calls + matching tool result)
        var messages = session.getContext().getMessages();
        assertEquals(1, messages.stream().filter(m -> "assistant".equals(m.role())
            && m.toolCalls() != null).count(), "exactly one round was committed");
        assertEquals(1, messages.stream().filter(m -> "tool".equals(m.role())
            && "c1".equals(m.toolCallId())).count(),
            "the backgrounded call's result must be committed with its tool_call_id");
    }

    @Test
    void aSecondTurnCanRunWhileTheFirstIsParkedInTheBackground() throws Exception {
        LlmSettings.INSTANCE.getBackgroundToolsEnabled().add(TestMcpToolProvider.ECHO);
        TestMcpToolProvider.ECHO_DELAY_MS = 600;

        var mock = new MockCompletions();
        // consumed FIFO: request 1 (loop 1) = the tool call; request 2 (loop 2, runs while
        // parked) = its answer; request 3 (loop 1 resume) = its answer
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{}")), ""));
        mock.thenRespond(MockCompletions.text("answer while parked"));
        mock.thenRespond(MockCompletions.text("first turn resumed"));

        var loop = new AgentLoop(session, mock);
        var beginResult = new CompletableFuture<AgentResult>();
        var thread = new Thread(
            () -> beginResult.complete(loop.begin("first", null, null, null)), "test-begin");
        thread.setDaemon(true);
        thread.start();

        Thread.sleep(150);
        loop.requestBackground();
        var paused = (AgentResult.PausedForBackground) beginResult.join();

        // a fresh loop (new turn) runs its own conversation from the current context
        var second = new AgentLoop(session, mock);
        var done2 = assertInstanceOf(AgentResult.Done.class,
            second.begin("while parked", null, null, null));
        assertEquals("answer while parked", done2.content(),
            "a new turn must be able to finish while the first is parked");
        assertTrue(!session.getContext().getMessages().isEmpty());
        // the parked round was not part of the context the second turn saw
        assertTrue(session.getContext().getMessages().stream()
            .filter(m -> "assistant".equals(m.role()) && m.toolCalls() != null).findFirst()
            .isEmpty(), "the parked round must still be staged");

        var output = waitForToolOutput(paused.jobId());
        session.getTurnQueue().poll();
        var resumed = loop.submitBackgroundOutput(paused.jobId(), output.content());
        assertEquals("first turn resumed", ((AgentResult.Done) resumed).content());
    }

    @Test
    void cancelWhileParkedDiscardsTheUnfinishedRound() throws Exception {
        LlmSettings.INSTANCE.getBackgroundToolsEnabled().add(TestMcpToolProvider.ECHO);
        TestMcpToolProvider.ECHO_DELAY_MS = 500;

        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{}")), ""));
        mock.thenRespond(MockCompletions.text("unused"));

        var loop = new AgentLoop(session, mock);
        var beginResult = new CompletableFuture<AgentResult>();
        var thread = new Thread(
            () -> beginResult.complete(loop.begin("go", null, null, null)), "test-begin");
        thread.setDaemon(true);
        thread.start();

        Thread.sleep(150);
        loop.requestBackground();
        var paused = (AgentResult.PausedForBackground) beginResult.join();

        loop.cancel();
        var output = waitForToolOutput(paused.jobId());
        session.getTurnQueue().poll();

        var resumed = loop.submitBackgroundOutput(paused.jobId(), output.content());
        assertInstanceOf(AgentResult.Done.class, resumed);
        assertTrue(((AgentResult.Done) resumed).content().contains("cancelled"));
        // the cancelled round must never appear in the context
        assertTrue(session.getContext().getMessages().stream()
            .noneMatch(m -> "assistant".equals(m.role()) && m.toolCalls() != null),
            "a cancelled round must not be committed");
    }

    /** Polls the session queue until the output of the given background job arrives. */
    private TurnQueue.ToolOutput waitForToolOutput(String jobId) throws InterruptedException {
        long deadline = System.currentTimeMillis() + 10_000;
        while (System.currentTimeMillis() < deadline) {
            for (var entry : session.getTurnQueue().snapshot()) {
                if (entry instanceof TurnQueue.ToolOutput out && out.jobId().equals(jobId)) {
                    return out;
                }
            }
            Thread.sleep(20);
        }
        throw new AssertionError("no ToolOutput for job " + jobId + " arrived in time");
    }
}
