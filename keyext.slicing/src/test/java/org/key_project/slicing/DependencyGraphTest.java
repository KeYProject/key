/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.graph.DependencyGraph;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the {@link DependencyGraph}.
 */
class DependencyGraphTest {
    @Test
    void basicTest() {
        var graph = new DependencyGraph();

        /*
         * Closed Goal FormulaE
         * | |
         * | Step3 | Step2
         * v v
         * FormulaB FormulaD
         * | \
         * | Step1 \ Step1
         * v v
         * FormulaA FormulaC
         */

        var formA = new TestGraphNode();
        var formB = new TestGraphNode();
        var formC = new TestGraphNode();
        var formD = new TestGraphNode();
        var formE = new TestGraphNode();
        var closedGoal = new TestClosedGoal();

        // Step 1
        graph.addRuleApplication(null,
            List.of(new Pair<>(formA, true), new Pair<>(formC, true)),
            List.of(formB));
        // Step 2
        graph.addRuleApplication(null,
            List.of(new Pair<>(formD, true)),
            List.of(formE));
        // Step 3
        graph.addRuleApplication(null,
            List.of(new Pair<>(formB, true)),
            List.of(closedGoal));

        assertEquals(6, graph.countNodes());
        assertEquals(4, graph.countEdges());

        var incomingClosedGoal =
            graph.incomingGraphEdgesOf(closedGoal).collect(Collectors.toList());
        assertEquals(1, incomingClosedGoal.size());
        assertEquals(formB, incomingClosedGoal.get(0).second);

        var incomingFormB = graph.incomingGraphEdgesOf(formB).collect(Collectors.toList());
        assertEquals(2, incomingFormB.size());
        if (incomingFormB.get(0).second.equals(formA)) {
            assertEquals(formC, incomingFormB.get(1).second);
        } else {
            assertEquals(formA, incomingFormB.get(1).second);
        }

        assertTrue(graph.containsNode(formA));
        assertTrue(graph.containsNode(formD));
        assertTrue(graph.containsNode(closedGoal));

        var neighborsB = graph.neighborsOf(formB).collect(Collectors.toList());
        assertEquals(3, neighborsB.size());
        assertTrue(neighborsB.contains(formA));
        assertTrue(neighborsB.contains(formC));
        assertTrue(neighborsB.contains(closedGoal));
    }
}
