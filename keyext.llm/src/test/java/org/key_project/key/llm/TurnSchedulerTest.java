/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import org.key_project.key.llm.AgentLoopTest.MockCompletions;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the {@link TurnScheduler}: it consumes the session's {@link TurnQueue} on its worker
 * thread, always accepts further prompts (they are queued while a turn runs), resumes parked turns
 * from question answers and background tool outputs, and reports everything through its
 * {@link TurnScheduler.TurnListener}.
 */
class TurnSchedulerTest {

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
    void multiplePromptsAreProcessedInOrder() throws Exception {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.text("answer one"));
        mock.thenRespond(MockCompletions.text("answer two"));
        var scheduler = new TurnScheduler(session, mock);
        var listener = new RecordingListener();
        scheduler.setListener(listener);

        // submitted back-to-back: the second one must be queued while the first runs
        scheduler.submitPrompt("one", null, null, null);
        scheduler.submitPrompt("two", null, null, null);

        assertTrue(listener.awaitDoneContent("answer one", 10_000));
        assertTrue(listener.awaitDoneContent("answer two", 10_000));
        assertEquals(List.of(), session.getTurnQueue().snapshot(), "the queue must drain");
        assertTrue(listener.queueEmpty(), "listener must observe the queue draining");
    }

    @Test
    void questionParksTheTurnAndTheAnswerResumesIt() throws Exception {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("q1", "ask_user",
                "{\"question\":\"split?\",\"options\":[\"yes\",\"no\"]}")),
            ""));
        mock.thenRespond(MockCompletions.text("resumed"));
        var scheduler = new TurnScheduler(session, mock);
        var listener = new RecordingListener();
        scheduler.setListener(listener);

        scheduler.submitPrompt("go", null, null, null);
        assertTrue(listener.awaitPaused(10_000), "the ask_user pause must be reported");

        scheduler.answer("yes");
        assertTrue(listener.awaitDoneContent("resumed", 10_000));
        var lastRequest = mock.sent.get(mock.sent.size() - 1).messages();
        var toolMsg = (java.util.Map<String, Object>) lastRequest.get(lastRequest.size() - 1);
        assertEquals("q1", toolMsg.get("tool_call_id"));
    }

    @Test
    void promptsAreDeferredWhileAQuestionIsParked() throws Exception {
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("q1", "ask_user", "{\"question\":\"sure?\"}")), ""));
        mock.thenRespond(MockCompletions.text("after question"));
        mock.thenRespond(MockCompletions.text("queued prompt answer"));
        var scheduler = new TurnScheduler(session, mock);
        var listener = new RecordingListener();
        scheduler.setListener(listener);

        scheduler.submitPrompt("first", null, null, null);
        assertTrue(listener.awaitPaused(10_000));
        // while the question is parked, further prompts must not start a second turn
        scheduler.submitPrompt("waiting", null, null, null);
        Thread.sleep(200);
        assertTrue(listener.results.isEmpty(),
            "no turn may run while a question is parked: " + listener.results);

        scheduler.answer("nope");
        assertTrue(listener.awaitDoneContent("after question", 10_000));
        assertTrue(listener.awaitDoneContent("queued prompt answer", 10_000));
    }

    @Test
    void backgroundedToolOutputResumesTheParkedTurnViaTheQueue() throws Exception {
        LlmSettings.INSTANCE.getBackgroundToolsEnabled().add(TestMcpToolProvider.ECHO);
        TestMcpToolProvider.ECHO_DELAY_MS = 600;
        var mock = new MockCompletions();
        mock.thenRespond(MockCompletions.toolCalls(
            List.of(MockCompletions.tool("c1", TestMcpToolProvider.ECHO, "{\"x\":2}")), ""));
        mock.thenRespond(MockCompletions.text("back from background"));
        var scheduler = new TurnScheduler(session, mock);
        var listener = new RecordingListener();
        scheduler.setListener(listener);

        scheduler.submitPrompt("go", null, null, null);
        // wait until the tool is running, then move it into the background
        assertTrue(listener.awaitToolStarted(10_000));
        Thread.sleep(150);
        scheduler.requestBackground();

        // the turn parks and the job is tracked
        assertTrue(listener.awaitBackgroundPark(10_000));
        assertTrue(scheduler.workerAlive());
        assertEquals(1, session.getBackgroundJobs().size());

        // once the call finishes, its output is enqueued and the parked turn resumes
        assertTrue(listener.awaitDoneContent("back from background", 10_000));
        assertEquals(0, session.getBackgroundJobs().size());
        assertTrue(session.getContext().getMessages().stream()
                .anyMatch(m -> "tool".equals(m.role()) && "c1".equals(m.toolCallId())),
            "the backgrounded call's result must land in the context");
    }

    /** Records the scheduler listener events (thread-safe; no EDT involvement). */
    static final class RecordingListener implements TurnScheduler.TurnListener {
        final List<String> results = new CopyOnWriteArrayList<>();
        final List<String> paused = new CopyOnWriteArrayList<>();
        final List<Integer> queueSizes = new CopyOnWriteArrayList<>();
        final CopyOnWriteArrayList<AgentResult.ToolCallInfo> started = new CopyOnWriteArrayList<>();

        @Override
        public void onResult(AgentResult result) {
            if (result instanceof AgentResult.Done done) {
                results.add(done.content());
            } else {
                results.add("FAILED");
            }
        }

        @Override
        public void onPaused(AgentResult result) {
            paused.add(result.getClass().getSimpleName());
        }

        @Override
        public void onQueueChanged(int queued) {
            queueSizes.add(queued);
        }

        @Override
        public void onJobsChanged(List<BackgroundJob> jobs) {
            // ignored here
        }

        @Override
        public void onToolStarted(AgentResult.ToolCallInfo info) {
            started.add(info);
        }

        @Override
        public void onToolFinished(String toolCallId, String outcome) {
            // ignored here
        }

        boolean queueEmpty() {
            return queueSizes.contains(0);
        }

        boolean awaitDoneContent(String content, long timeoutMs) throws InterruptedException {
            long deadline = System.currentTimeMillis() + timeoutMs;
            while (System.currentTimeMillis() < deadline) {
                if (results.contains(content)) {
                    return true;
                }
                Thread.sleep(20);
            }
            return results.contains(content);
        }

        boolean awaitPaused(long timeoutMs) throws InterruptedException {
            return awaitPausedClass("NeedsInput", timeoutMs) || awaitPausedClass("NeedsApproval",
                timeoutMs) || awaitPausedClass("PausedForBackground", timeoutMs);
        }

        boolean awaitBackgroundPark(long timeoutMs) throws InterruptedException {
            return awaitPausedClass("PausedForBackground", timeoutMs);
        }

        boolean awaitToolStarted(long timeoutMs) throws InterruptedException {
            long deadline = System.currentTimeMillis() + timeoutMs;
            while (System.currentTimeMillis() < deadline) {
                if (!started.isEmpty()) {
                    return true;
                }
                Thread.sleep(20);
            }
            return !started.isEmpty();
        }

        private boolean awaitPausedClass(String clazz, long timeoutMs)
                throws InterruptedException {
            long deadline = System.currentTimeMillis() + timeoutMs;
            while (System.currentTimeMillis() < deadline) {
                if (paused.contains(clazz)) {
                    return true;
                }
                Thread.sleep(20);
            }
            return paused.contains(clazz);
        }
    }
}
