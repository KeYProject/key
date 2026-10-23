/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;

/**
 * A bounded, thread-safe record of finished sub-agent runs of one {@link LlmSession}, for
 * observability: the {@code get_subagent_logs} tool renders it for the model, and the chat panel
 * shows the newest run's per-task lines indented under the {@code spawn_subagent} activity.
 * <p>
 * Runs are stored oldest first and pruned from the head once the capacity is exceeded. The
 * sequence numbers are monotonically increasing and never reused, so a caller can snapshot the
 * head of the log ({@link #latestSeq()}) and later ask for everything appended since then
 * ({@link #after(long)}) without being confused by pruning.
 *
 * @author Alexander Weigl
 */
public class SubagentLog {

    /** Default bound on the number of kept runs. */
    public static final int DEFAULT_CAPACITY = 25;

    /** How one delegated task of a sub-agent run ended. */
    public enum Status {
        OK("OK"),
        STOPPED("stopped (round limit)"),
        CANCELLED("cancelled"),
        FAILED("failed");

        private final String label;

        Status(String label) {
            this.label = label;
        }

        /** Short human-readable label used in the log output. */
        public String label() {
            return label;
        }
    }

    /**
     * The outcome of one delegated task (the single task of a sequential run, or one task of a
     * parallel batch).
     */
    public record SubagentTask(String task, Status status, int rounds, List<String> tools,
            String outcome) {
    }

    /** One finished {@code spawn_subagent} call: roles, mode, timing and the per-task outcomes. */
    public record SubagentRun(long seq, String role, String mode, long startedAt, long durationMs,
            List<SubagentTask> tasks) {
    }

    private final ArrayDeque<SubagentRun> runs = new ArrayDeque<>();
    private final int capacity;
    private long seq = 0;

    public SubagentLog() {
        this(DEFAULT_CAPACITY);
    }

    public SubagentLog(int capacity) {
        this.capacity = Math.max(1, capacity);
    }

    /** Appends a run (assigning its sequence number) and returns the stored record. */
    public synchronized SubagentRun add(SubagentRun run) {
        var stored = new SubagentRun(++seq, run.role(), run.mode(), run.startedAt(),
            run.durationMs(), run.tasks());
        runs.addLast(stored);
        while (runs.size() > capacity) {
            runs.removeFirst();
        }
        return stored;
    }

    /** The sequence number of the newest run, or 0 when the log is empty. */
    public synchronized long latestSeq() {
        return runs.isEmpty() ? 0 : runs.getLast().seq();
    }

    /** All runs with a sequence number greater than {@code seq}, oldest first. */
    public synchronized List<SubagentRun> after(long seq) {
        return runs.stream().filter(r -> r.seq() > seq).toList();
    }

    /** The newest runs, newest first, capped at {@code limit} (0 = uncapped snapshot of all). */
    public synchronized List<SubagentRun> snapshot(int limit) {
        var out = new ArrayList<SubagentRun>();
        var it = runs.descendingIterator();
        while (it.hasNext() && (limit <= 0 || out.size() < limit)) {
            out.add(it.next());
        }
        return out;
    }

    public synchronized int size() {
        return runs.size();
    }

    public synchronized void clear() {
        runs.clear();
    }
}
