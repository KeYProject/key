/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.io.File;
import java.util.Collection;

import de.uka.ilkd.key.control.KeYEnvironment;

import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.TrackedFunction;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class FunctionTrackerTest {
    public static final File TEST_CASES_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    void tracksSkolemConstantCorrectly() throws Exception {
        var file = new File(TEST_CASES_DIRECTORY, "testFunctionTracker.proof");
        var env = KeYEnvironment.load(file);
        var proof = env.getLoadedProof();
        var tracker = new DependencyTracker(proof);
        var depGraph = tracker.getDependencyGraph();
        Collection<AnnotatedEdge> edges = depGraph.edgesOf(proof.findAny(x -> x.serialNr() == 4));
        assertEquals(2, edges.size());
        var edge = edges.stream().findFirst().get();
        assertInstanceOf(TrackedFunction.class, edge.getSource());
    }
}
