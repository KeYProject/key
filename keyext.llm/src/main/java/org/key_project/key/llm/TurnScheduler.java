/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.function.Supplier;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.TurnQueue.UserPrompt;

import org.jspecify.annotations.Nullable;

/**
 * The per-session turn scheduler: a single worker thread consumes the session's {@link TurnQueue}
 * and drives the {@link AgentLoop}s - one turn at a time. While a turn is running, further user
 * prompts are simply queued (input is always accepted); when a turn parks - on a question, an
 * approval or a backgrounded tool call - the scheduler resumes it as soon as the corresponding
 * queue entry arrives.
 * <p>
 * Parking rules:
 * <ul>
 * <li>a turn parked on a {@code ask_user} question or a tool approval holds all further user
 * prompts until it is resumed or stopped (the answer/decision is user interaction with that
 * turn),</li>
 * <li>a turn parked on a background tool call does <em>not</em> block: further user prompts start
 * fresh turns while the background job runs; when the job finishes its output is enqueued and the
 * parked turn resumes.</li>
 * </ul>
 * <p>
 * The listener callbacks are invoked on the scheduler thread; the UI must forward them to the EDT
 * itself. The scheduler object is cheap to create - its worker thread only starts on the first
 * submitted prompt.
 *
 * @author Alexander Weigl
 */
public final class TurnScheduler {
    private final LlmSession session;
    private final ChatCompletionsClient completions;
    private final TurnQueue queue;

    private final Thread worker;
    private volatile boolean stopped = false;

    private @Nullable TurnListener listener;
    private @Nullable AgentLoop activeLoop;
    private @Nullable AgentLoop pendingQuestion;
    private @Nullable AgentLoop pendingApproval;
    private @Nullable UserPrompt deferred;

    /** Callbacks fired by the scheduler as turns progress (on the scheduler thread). */
    public interface TurnListener {
        /** A turn ended (final answer or error). */
        void onResult(AgentResult result);

        /** A turn parked for user interaction (question, approval or background). */
        void onPaused(AgentResult result);

        /** The number of queued entries changed. */
        void onQueueChanged(int queued);

        /** The set of running background jobs changed. */
        void onJobsChanged(List<BackgroundJob> jobs);

        /** A tool call started executing (for the live running-tool row). */
        void onToolStarted(AgentResult.ToolCallInfo info);

        /** A foreground tool call finished; {@code outcome} is the tool-result text. */
        void onToolFinished(String toolCallId, String outcome);
    }

    /** Tool-lifecycle events reported by the agent loop while it runs tools. */
    public interface ToolObserver {
        void toolStarted(AgentResult.ToolCallInfo info);

        void toolFinished(String toolCallId, String outcome);
    }

    public TurnScheduler(LlmSession session, ChatCompletionsClient completions) {
        this.session = session;
        this.completions = completions;
        this.queue = session.getTurnQueue();
        session.setTurnObserver(new ToolObserver() {
            @Override
            public void toolStarted(AgentResult.ToolCallInfo info) {
                var l = listener;
                if (l != null) {
                    l.onToolStarted(info);
                }
            }

            @Override
            public void toolFinished(String toolCallId, String outcome) {
                var l = listener;
                if (l != null) {
                    l.onToolFinished(toolCallId, outcome);
                }
            }
        });
        session.getBackgroundJobs().setOnChange(this::fireJobsChanged);
        worker = new Thread(this::run, "llm-turn-scheduler");
        worker.setDaemon(true);
    }

    /** Registers the UI listener; replaces any previous listener. */
    public void setListener(@Nullable TurnListener listener) {
        this.listener = listener;
    }

    /** Starts the worker thread (idempotent); called lazily on the first submitted prompt. */
    public synchronized void start() {
        if (!worker.isAlive()) {
            worker.start();
        }
    }

    /** Whether the worker thread is running. */
    public boolean workerAlive() {
        return worker.isAlive();
    }

    // ------------------------------------------------------------------ user-facing API

    /** Queues a new user prompt; starts a fresh turn when the scheduler is able to. */
    public void submitPrompt(String text, @Nullable Proof proof, @Nullable Node node,
            @Nullable Skill skill) {
        start();
        queue.enqueue(new TurnQueue.UserPrompt(text, proof, node, skill));
        fireQueueChanged();
    }

    /** Queues the answer to the pending {@code ask_user} question. */
    public void answer(String answer) {
        start();
        queue.enqueue(new TurnQueue.QuestionAnswer(answer));
        fireQueueChanged();
    }

    /** Queues the user's decision on the pending tool approval. */
    public void decide(boolean allow, boolean always) {
        start();
        queue.enqueue(new TurnQueue.ApprovalDecision(allow, always));
        fireQueueChanged();
    }

    /** Cancels the current turn (the tool it is waiting for keeps running in the background). */
    public void requestStop() {
        var loop = activeLoop;
        if (loop == null) {
            return;
        }
        loop.cancel();
        if (pendingQuestion == loop) {
            pendingQuestion = null;
            fireQueueChanged();
        }
        if (pendingApproval == loop) {
            pendingApproval = null;
            fireQueueChanged();
        }
    }

    /** Moves the currently running tool call of the active turn into the background, if possible. */
    public void requestBackground() {
        var loop = activeLoop;
        if (loop != null) {
            loop.requestBackground();
        }
    }

    /** Cancels the given background job; its output is delivered as a cancellation note. */
    public void cancelJob(String jobId) {
        session.getBackgroundJobs().cancel(jobId);
        fireJobsChanged();
    }

    // ------------------------------------------------------------------ worker loop

    private void run() {
        while (!stopped) {
            final TurnQueue.Entry entry;
            try {
                entry = queue.take();
            } catch (InterruptedException e) {
                if (stopped) {
                    break;
                }
                continue;
            }
            process(entry);
            fireQueueChanged();
            fireJobsChanged();
            if (deferred != null && pendingQuestion == null && pendingApproval == null) {
                var prompt = deferred;
                deferred = null;
                startTurn(prompt);
            }
        }
    }

    private void process(TurnQueue.Entry entry) {
        switch (entry) {
            case TurnQueue.UserPrompt p -> {
                if (pendingQuestion != null || pendingApproval != null) {
                    deferred = p;
                    return;
                }
                startTurn(p);
            }
            case TurnQueue.QuestionAnswer a -> {
                var loop = pendingQuestion;
                if (loop == null) {
                    fireResult(new AgentResult.Failed(
                        new IllegalStateException("No pending question to answer.")));
                    return;
                }
                pendingQuestion = null;
                drive(loop, () -> loop.answerQuestion(a.answer()));
            }
            case TurnQueue.ApprovalDecision d -> {
                var loop = pendingApproval;
                if (loop == null) {
                    fireResult(new AgentResult.Failed(
                        new IllegalStateException("No pending approval to decide.")));
                    return;
                }
                pendingApproval = null;
                drive(loop, () -> loop.decideApproval(d.allow(), d.always()));
            }
            case TurnQueue.ToolOutput t -> {
                var job = session.getBackgroundJobs().take(t.jobId());
                if (job == null) {
                    return;
                }
                drive(job.loop(), () -> job.loop().submitBackgroundOutput(t.jobId(), t.content()));
            }
        }
    }

    private void startTurn(TurnQueue.UserPrompt p) {
        var loop = new AgentLoop(session, completions);
        drive(loop, () -> loop.begin(p.rawText(), p.proof(), p.node(), p.skill()));
    }

    private void drive(AgentLoop loop, Supplier<AgentResult> action) {
        activeLoop = loop;
        AgentResult result;
        try {
            result = action.get();
        } catch (Exception e) {
            result = new AgentResult.Failed(e);
        }
        switch (result) {
            case AgentResult.Done done -> {
                if (activeLoop == loop) {
                    activeLoop = null;
                }
                fireResult(new AgentResult.Done(done.content(), done.activities()));
            }
            case AgentResult.Failed failed -> {
                if (activeLoop == loop) {
                    activeLoop = null;
                }
                fireResult(failed);
            }
            case AgentResult.NeedsInput q -> {
                pendingQuestion = loop;
                firePaused(q);
            }
            case AgentResult.NeedsApproval approval -> {
                pendingApproval = loop;
                firePaused(approval);
            }
            case AgentResult.PausedForBackground pb -> firePaused(pb);
        }
    }

    private void fireQueueChanged() {
        var l = listener;
        if (l != null) {
            l.onQueueChanged(queue.size());
        }
    }

    private void fireJobsChanged() {
        var l = listener;
        if (l != null) {
            l.onJobsChanged(session.getBackgroundJobs().snapshot());
        }
    }

    private void fireResult(AgentResult result) {
        var l = listener;
        if (l != null) {
            l.onResult(result);
        }
    }

    private void firePaused(AgentResult result) {
        var l = listener;
        if (l != null) {
            l.onPaused(result);
        }
    }
}
