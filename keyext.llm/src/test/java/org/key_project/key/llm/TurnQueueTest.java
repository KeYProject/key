/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the FIFO {@link TurnQueue}: ordering, the blocking {@code take()} and the queue entry
 * kinds that drive a turn (user prompt, background tool output, question answer, approval).
 */
class TurnQueueTest {

    @Test
    void entriesAreConsumedInFifoOrder() {
        var queue = new TurnQueue();
        queue.enqueue(new TurnQueue.UserPrompt("first", null, null, null));
        queue.enqueue(new TurnQueue.ToolOutput("bg-1", "output"));
        queue.enqueue(new TurnQueue.QuestionAnswer("yes"));

        assertEquals(3, queue.size());
        assertInstanceOf(TurnQueue.UserPrompt.class, queue.poll());
        assertInstanceOf(TurnQueue.ToolOutput.class, queue.poll());
        assertInstanceOf(TurnQueue.QuestionAnswer.class, queue.poll());
        assertNull(queue.poll(), "queue must be empty after polling everything");
        assertEquals(0, queue.size());
    }

    @Test
    void pollReturnsNullWhenEmpty() {
        var queue = new TurnQueue();
        assertNull(queue.poll());
        assertEquals(List.of(), queue.snapshot());
    }

    @Test
    void snapshotCopiesThePendingEntries() {
        var queue = new TurnQueue();
        queue.enqueue(new TurnQueue.ApprovalDecision(true, false));
        queue.enqueue(new TurnQueue.UserPrompt("hello", null, null, null));

        var snapshot = queue.snapshot();
        assertEquals(2, snapshot.size());
        // a snapshot is detached
        queue.poll();
        assertEquals(2, snapshot.size());
    }

    @Test
    void takeBlocksUntilAnEntryIsEnqueued() throws InterruptedException {
        var queue = new TurnQueue();
        var taken = new AtomicReference<TurnQueue.Entry>();
        var latch = new CountDownLatch(1);
        var thread = new Thread(() -> {
            try {
                taken.set(queue.take());
                latch.countDown();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }, "queue-take-test");
        thread.setDaemon(true);
        thread.start();

        assertTrue(!latch.await(150, TimeUnit.MILLISECONDS),
            "take() must block while the queue is empty");

        queue.enqueue(new TurnQueue.UserPrompt("wake up", null, null, null));
        assertTrue(latch.await(5, TimeUnit.SECONDS), "enqueue must wake a blocked take()");
        var entry = taken.get();
        assertInstanceOf(TurnQueue.UserPrompt.class, entry);
        assertEquals("wake up", ((TurnQueue.UserPrompt) entry).rawText());
    }
}
