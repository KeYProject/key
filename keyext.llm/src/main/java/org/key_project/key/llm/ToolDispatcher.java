/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.function.Supplier;

/**
 * The shared tool dispatcher of KeY-Agent sessions. It owns the pool on which tool calls run and
 * the single lock that serializes every dispatch, because KeY proofs, the GUI mediator and the
 * chat-completion endpoint are not thread-safe (only one proof-mutating or model-mutating call may
 * execute at a time; independent parallel sub-agents still run concurrently and just serialize on
 * this lock).
 * <p>
 * Three entry points:
 * <ul>
 * <li>{@link #submit(LlmSession, String, String)} - asynchronous, serialized dispatch of a normal
 * tool call; the returned future completes with the tool result (or a {@link CompletionException}
 * wrapping the tool error). Used by the agent loop, which polls the future so it can honor
 * cancellation and user-initiated backgrounding while the call runs.</li>
 * <li>{@link #submitTask(Supplier)} - asynchronous execution of an arbitrary task <em>without</em>
 * the dispatch lock; used for {@code spawn_subagent}, whose children acquire the lock themselves
 * per child tool call (holding it across the whole delegation would deadlock parallel
 * fan-out).</li>
 * <li>{@link #callNow(LlmSession, String, String)} - synchronous serialized dispatch; used by the
 * sub-agent child loops, which are already running on a dispatcher thread and must not spawn
 * more.</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class ToolDispatcher {
    /**
     * The process-wide dispatcher (the dispatch lock used to be a static field of SubagentRunner).
     */
    public static final ToolDispatcher INSTANCE = new ToolDispatcher();

    private final Object dispatchLock = new Object();
    private final ExecutorService pool;

    private ToolDispatcher() {
        pool = Executors.newCachedThreadPool(r -> {
            var t = new Thread(r, "key-tool-dispatch");
            t.setDaemon(true);
            return t;
        });
    }

    /**
     * Asynchronously runs a normal tool call on the dispatcher pool, serialized against all other
     * dispatches. The model-visible tool result is {@code stringify}ed on completion.
     */
    public CompletableFuture<Object> submit(LlmSession session, String name, String arguments) {
        return CompletableFuture.supplyAsync(() -> {
            synchronized (dispatchLock) {
                return callLocked(session, name, arguments);
            }
        }, pool);
    }

    /**
     * Asynchronously runs an arbitrary task on the dispatcher pool <em>without</em> the dispatch
     * lock (sub-agent delegation; the child loops serialize their own tool calls via
     * {@link #callNow}).
     */
    public <T> CompletableFuture<T> submitTask(Supplier<T> task) {
        return CompletableFuture.supplyAsync(task, pool);
    }

    /**
     * Synchronously runs a tool call on the calling thread while holding the dispatch lock
     * (sub-agent child loops). Returns the stringified tool result.
     *
     * @throws Exception the tool error
     */
    public String callNow(LlmSession session, String name, String arguments) throws Exception {
        synchronized (dispatchLock) {
            return AgentLoop.stringify(callLocked(session, name, arguments));
        }
    }

    /** Runs the given task while holding the dispatch lock (used by tests and one-off code). */
    public <T> T callSynchronized(Supplier<T> task) {
        synchronized (dispatchLock) {
            return task.get();
        }
    }

    private Object callLocked(LlmSession session, String name, String arguments) {
        try {
            return session.getMcpClient().callTool(name, arguments);
        } catch (Exception e) {
            throw new CompletionException(e);
        }
    }
}
