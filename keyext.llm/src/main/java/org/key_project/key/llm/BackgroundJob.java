/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.concurrent.CompletableFuture;

/**
 * A tool call moved into the background by the user. The call keeps running on the
 * {@link ToolDispatcher} pool; when it finishes, its output is enqueued as a
 * {@link TurnQueue.ToolOutput} into the owning session's queue and the parked
 * {@link AgentLoop} resumes with it.
 * <p>
 * Instances are created by {@link BackgroundJobRegistry#start}. The only mutable state is the
 * cancelled flag: a cancelled job still runs to completion (proof tools are not interruptible),
 * but its output is reported to the agent as cancelled.
 *
 * @author Alexander Weigl
 */
public final class BackgroundJob {
    private final String jobId;
    private final AgentLoop loop;
    private final String toolCallId;
    private final String toolName;
    private final String arguments;
    private final CompletableFuture<?> future;
    private volatile boolean cancelled;

    BackgroundJob(String jobId, AgentLoop loop, String toolCallId, String toolName,
            String arguments, CompletableFuture<?> future) {
        this.jobId = jobId;
        this.loop = loop;
        this.toolCallId = toolCallId;
        this.toolName = toolName;
        this.arguments = arguments;
        this.future = future;
    }

    /** The unique job identifier (the key of the {@link TurnQueue.ToolOutput}). */
    public String jobId() {
        return jobId;
    }

    /** The parked agent turn that awaits this job's output. */
    public AgentLoop loop() {
        return loop;
    }

    /** The tool call id within the round (for the tool result message). */
    public String toolCallId() {
        return toolCallId;
    }

    /** The name of the running tool. */
    public String toolName() {
        return toolName;
    }

    /** The tool call arguments. */
    public String arguments() {
        return arguments;
    }

    /** The running call; when it completes the registry enqueues the output. */
    public CompletableFuture<?> future() {
        return future;
    }

    /** Marks the job as cancelled; the running call itself is not interrupted. */
    void setCancelled() {
        cancelled = true;
    }

    /** Whether the user cancelled this background job. */
    public boolean isCancelled() {
        return cancelled;
    }
}
