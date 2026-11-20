/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.atomic.AtomicLong;

import org.jspecify.annotations.Nullable;

/**
 * Tracks the background tool calls of one {@link LlmSession} (per-proof). A job is created when
 * the user moves a running tool call into the background; the registry keeps it visible while the
 * call runs and delivers its output as a {@link TurnQueue.ToolOutput} into the session's queue
 * when it completes, so the {@link TurnScheduler} can resume the parked turn.
 * <p>
 * The registry is not expected to outlive its session's turns; entries are added on
 * backgrounding and removed when the {@link TurnScheduler} picks up the finished job's output.
 *
 * @author Alexander Weigl
 */
public final class BackgroundJobRegistry {
    private static final AtomicLong SEQ = new AtomicLong();

    private final TurnQueue queue;
    private final Map<String, BackgroundJob> jobs = new LinkedHashMap<>();
    private @Nullable Runnable onChange;

    public BackgroundJobRegistry(TurnQueue queue) {
        this.queue = queue;
    }

    /** Callback fired whenever the job set changes (registration, completion, removal). */
    public void setOnChange(@Nullable Runnable onChange) {
        this.onChange = onChange;
    }

    /**
     * Registers a new background job and wires the completion handler that enqueues its output.
     *
     * @param loop the parked turn awaiting the output
     * @param toolCallId the tool call id within the round
     * @param toolName the running tool
     * @param arguments the tool call arguments
     * @param future the running call
     * @return the created job
     */
    public BackgroundJob start(AgentLoop loop, String toolCallId, String toolName, String arguments,
            CompletableFuture<?> future) {
        String jobId = "bg-" + SEQ.incrementAndGet();
        var job = new BackgroundJob(jobId, loop, toolCallId, toolName, arguments, future);
        synchronized (jobs) {
            jobs.put(jobId, job);
        }
        future.whenComplete((value, error) -> {
            String content = job.isCancelled() ? "[Background job cancelled by the user: "
                + toolName + "]" : format(value, error);
            queue.enqueue(new TurnQueue.ToolOutput(jobId, content));
            fireChanged();
        });
        fireChanged();
        return job;
    }

    /** Removes and returns the job with the given id, or {@code null} when unknown. */
    public @Nullable BackgroundJob take(String jobId) {
        synchronized (jobs) {
            var removed = jobs.remove(jobId);
            if (removed != null) {
                fireChanged();
            }
            return removed;
        }
    }

    /** Marks the job as cancelled; its output is delivered as a cancellation note. */
    public void cancel(String jobId) {
        synchronized (jobs) {
            var job = jobs.get(jobId);
            if (job != null) {
                job.setCancelled();
                fireChanged();
            }
        }
    }

    /** The number of currently running background jobs. */
    public int size() {
        synchronized (jobs) {
            return jobs.size();
        }
    }

    /**
     * Whether another background job may be started (reads the {@code maxBackgroundJobs} setting).
     */
    public boolean canStartMore(int maxBackgroundJobs) {
        return size() < Math.max(1, maxBackgroundJobs);
    }

    /** A snapshot of the currently running jobs (insertion order). */
    public List<BackgroundJob> snapshot() {
        synchronized (jobs) {
            return List.copyOf(jobs.values());
        }
    }

    private void fireChanged() {
        var cb = onChange;
        if (cb != null) {
            cb.run();
        }
    }

    private static String format(Object value, Throwable error) {
        if (error != null) {
            var cause = error instanceof CompletionException ce && ce.getCause() != null
                    ? ce.getCause()
                    : error;
            return "Error: " + (cause.getMessage() == null ? cause.toString()
                    : cause.getMessage());
        }
        return AgentLoop.stringify(value);
    }
}
