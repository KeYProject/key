/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests that {@link BoundedProgramVariableCollector} collects the same variables as
 * {@link ProgramVariableCollector} when restricted to the variables of interest -- i.e. its early
 * exit never loses an interested variable -- and that it does in fact stop early.
 */
public class TestBoundedProgramVariableCollector {

    private static final String[] BLOCKS = {
        "{ int j1 = 0; int j2, j3, j4 = 0; }",
        "{ int j1; for (int j4 = 0; j4 < 3; j4++) { j1 = j4; } int j5; }",
        "{ int j0; { { int j1; } int j2; } int j3; }" };

    private static Set<LocationVariable> fullCollect(ProgramElement prog, Services services) {
        ProgramVariableCollector pvc = new ProgramVariableCollector(prog, services);
        pvc.start();
        return new LinkedHashSet<>(pvc.result());
    }

    private static Set<LocationVariable> boundedCollect(ProgramElement prog, Services services,
            Set<LocationVariable> interested) {
        BoundedProgramVariableCollector bpvc =
            new BoundedProgramVariableCollector(prog, services, interested);
        bpvc.start();
        return new LinkedHashSet<>(bpvc.result());
    }

    private static Set<LocationVariable> intersect(Set<LocationVariable> a,
            Set<LocationVariable> b) {
        Set<LocationVariable> r = new LinkedHashSet<>(a);
        r.retainAll(b);
        return r;
    }

    @Test
    public void testIntersectionMatchesFullCollector() {
        final Services services = TacletForTests.services();
        final JavaService r2k = services.getJavaService();
        for (String b : BLOCKS) {
            final ProgramElement prog = r2k.readBlockWithEmptyContext(b, null).program();
            final Set<LocationVariable> full = fullCollect(prog, services);

            // the empty interest set: nothing is searched for
            assertEquals(Set.of(), intersect(boundedCollect(prog, services, new LinkedHashSet<>()),
                Set.of()), b);

            // every singleton subset, plus the whole set: result restricted to the interest set
            // must equal the full collection restricted to it (early exit loses nothing).
            for (LocationVariable v : full) {
                Set<LocationVariable> interested = new LinkedHashSet<>();
                interested.add(v);
                assertEquals(intersect(full, interested),
                    intersect(boundedCollect(prog, services, interested), interested),
                    "single var " + v + " in " + b);
            }
            assertEquals(full, intersect(boundedCollect(prog, services, new LinkedHashSet<>(full)),
                full), "all vars in " + b);
        }
    }

    @Test
    public void testEarlyExit() {
        final Services services = TacletForTests.services();
        final JavaService r2k = services.getJavaService();
        // a block where a variable is used early and many statements follow it
        final ProgramElement prog = r2k.readBlockWithEmptyContext(
            "{ int a = 0; int b1; int b2; int b3; int b4; int b5; }", null).program();
        final Set<LocationVariable> full = fullCollect(prog, services);

        LocationVariable a = full.stream().filter(v -> v.name().toString().equals("a")).findFirst()
                .orElseThrow();
        Set<LocationVariable> interested = new LinkedHashSet<>();
        interested.add(a);
        Set<LocationVariable> bounded = boundedCollect(prog, services, interested);

        // it found what we asked for ...
        assertTrue(bounded.contains(a), "bounded collector must find the interested variable");
        // ... and stopped before collecting the whole block (a appears in the first statement).
        assertTrue(bounded.size() < full.size(),
            "bounded collector should stop early: collected " + bounded + " of " + full);
    }
}
