/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayDeque;
import java.util.List;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.Nullable;

/**
 * The FIFO message queue of a {@link LlmSession}: everything that drives a turn is submitted
 * through this queue, so the user can always enter input (even while a turn is running) and it is
 * processed in order by the session's {@link TurnScheduler}.
 * <p>
 * Entry kinds:
 * <ul>
 * <li>{@link UserPrompt} - a new user message; starts a fresh turn (processed immediately unless
 * another turn is parked on a question or approval).</li>
 * <li>{@link ToolOutput} - a background tool call finished; resumes the parked turn of the
 * background job.</li>
 * <li>{@link QuestionAnswer} - the user answered an {@code ask_user} question; resumes the parked
 * question turn.</li>
 * <li>{@link ApprovalDecision} - the user decided on a tool approval; resumes the parked approval
 * turn.</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class TurnQueue {
    private final ArrayDeque<Entry> queue = new ArrayDeque<>();
    private final Object lock = new Object();

    /** A queued turn-driving event (see the class javadoc). */
    public sealed interface Entry permits UserPrompt, ToolOutput, QuestionAnswer, ApprovalDecision {
    }

    /** A new user message. */
    public record UserPrompt(String rawText, @Nullable Proof proof, @Nullable Node node,
            @Nullable Skill skill) implements Entry {
    }

    /** A background tool call completed; {@code content} is the tool-result text. */
    public record ToolOutput(String jobId, String content) implements Entry {
    }

    /** The user answered an {@code ask_user} question. */
    public record QuestionAnswer(String answer) implements Entry {
    }

    /** The user decided on a tool approval. */
    public record ApprovalDecision(boolean allow, boolean always) implements Entry {
    }

    /** Appends an entry and wakes up a blocked {@link #take()}. */
    public void enqueue(Entry entry) {
        synchronized (lock) {
            queue.addLast(entry);
            lock.notifyAll();
        }
    }

    /** Returns the head entry, blocking until one is available. */
    public Entry take() throws InterruptedException {
        synchronized (lock) {
            while (queue.isEmpty()) {
                lock.wait();
            }
            return queue.removeFirst();
        }
    }

    /** Removes and returns the head entry, or {@code null} when empty. */
    public @Nullable Entry poll() {
        synchronized (lock) {
            return queue.pollFirst();
        }
    }

    /** The number of queued entries. */
    public int size() {
        synchronized (lock) {
            return queue.size();
        }
    }

    /** A snapshot of the currently queued entries (newest last). */
    public List<Entry> snapshot() {
        synchronized (lock) {
            return List.copyOf(queue);
        }
    }
}
