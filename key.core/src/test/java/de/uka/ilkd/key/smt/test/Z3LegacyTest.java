/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;

import java.util.stream.Stream;

import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.junit.jupiter.params.provider.Arguments;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth.*;
import static de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth.VALID;

/**
 * Tests that some simple .key files are translated to SMT-LIB correctly and Z3 has a specified
 * behavior on them (returns unsat, sat, or unknown/timeout). The test uses the old and non-modular
 * SMT translation!
 * <p>
 * Note: The settings for the solver are hard-coded in {@link de.uka.ilkd.key.smt.SMTTestSettings}!
 */
public class Z3LegacyTest extends SMTSolverTest {
    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(Z3LegacyTest.class);
    private static final String SOLVER_NAME = "Z3 (Legacy Translation)";
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals(SOLVER_NAME))
            .findFirst().orElse(null);

    @Override
    protected Logger getLogger() {
        return LOGGER;
    }

    @Override
    protected String getSystemPropertySolverPath() {
        return SYSTEM_PROPERTY_SOLVER_PATH;
    }

    @Override
    protected String getSolverName() {
        return SOLVER_NAME;
    }

    @Override
    public SolverType getSolverType() {
        SolverType type = Z3_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }

    @Override
    protected Stream<Arguments> provideTestData() {
        return Stream.of(
            Arguments.of(FALSIFIABLE, "andnot.key"),
            Arguments.of(VALID, "ornot.key"),
            Arguments.of(FALSIFIABLE, "andornot.key"),
            Arguments.of(VALID, "andornot2.key"),
            Arguments.of(VALID, "imply.key"),
            Arguments.of(VALID, "imply2.key"),
            Arguments.of(FALSIFIABLE, "imply3.key"),
            Arguments.of(VALID, "equi1.key"),
            Arguments.of(FALSIFIABLE, "equi2.key"),
            Arguments.of(VALID, "allex1.key"),
            Arguments.of(FALSIFIABLE, "allex2.key"),
            Arguments.of(VALID, "allex3.key"),
            Arguments.of(VALID, "logicalite1.key"),
            Arguments.of(FALSIFIABLE, "logicalite2.key"),
            Arguments.of(VALID, "equal1.key"),
            // Arguments.of(FALSIFIABLE, "equal2.key"), // disabled because it takes too long in CI
            Arguments.of(VALID, "subsort1.key"),
            // Arguments.of(FALSIFIABLE, "subsort2.key"), // only with old z3 versions (e.g. 4.9.x)
            Arguments.of(VALID, "add1.key"),
            Arguments.of(VALID, "bsum1.key"),
            Arguments.of(VALID, "bsum2.key"),
            Arguments.of(UNKNOWN, "bsum3.key"), // timeout expected
            Arguments.of(VALID, "bprod1.key"),
            Arguments.of(VALID, "bprod2.key"),
            Arguments.of(UNKNOWN, "bprod3.key"), // timeout expected
            Arguments.of(VALID, "binder4.key"),
            Arguments.of(VALID, "binder5.key"),
            Arguments.of(VALID, "div1.key"),
            Arguments.of(VALID, "div3.key"),
            Arguments.of(UNKNOWN, "div5.key"), // timeout expected
            Arguments.of(UNKNOWN, "div6.key") // timeout expected
        );
    }
}
