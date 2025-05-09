/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import org.junit.jupiter.params.provider.Arguments;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.stream.Stream;

import static de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth.UNKNOWN;
import static de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth.VALID;

/**
 * Tests that some simple .key files are translated to SMT-LIB correctly and cvc5 has a specified
 * behavior on them (returns unsat, sat, or unknown/timeout). The test uses the new modular SMT
 * translation!
 * <p>
 * Note: The settings for the solver are hard-coded in {@link de.uka.ilkd.key.smt.SMTTestSettings}!
 */
public class Cvc5Test extends SMTSolverTest {


    public static final String SYSTEM_PROPERTY_SOLVER_PATH = "cvc5SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(Cvc5Test.class);
    private static final String SOLVER_NAME = "cvc5";

    private static final SolverType CVC5_SOLVER = SolverTypes.getSolverTypes().stream()
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
        SolverType type = CVC5_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }

    @Override
    protected final Stream<Arguments> provideTestData() {
        return Stream.of(
            Arguments.of(UNKNOWN, "andnot.key"), // timeout expected
            Arguments.of(VALID, "ornot.key"),
            Arguments.of(UNKNOWN, "andornot.key"), // timeout expected
            Arguments.of(VALID, "andornot2.key"),
            Arguments.of(VALID, "imply.key"),
            Arguments.of(VALID, "imply2.key"),
            Arguments.of(UNKNOWN, "imply3.key"), // timeout expected
            Arguments.of(VALID, "equi1.key"),
            Arguments.of(UNKNOWN, "equi2.key"), // timeout expected
            Arguments.of(VALID, "allex1.key"),
            Arguments.of(UNKNOWN, "allex2.key"), // timeout expected
            Arguments.of(UNKNOWN, "allex3.key"),
            Arguments.of(VALID, "logicalite1.key"),
            Arguments.of(UNKNOWN, "logicalite2.key"), // timeout expected
            Arguments.of(VALID, "equal1.key"),
            Arguments.of(UNKNOWN, "equal2.key"), // timeout expected
            Arguments.of(VALID, "subsort1.key"),
            Arguments.of(UNKNOWN, "subsort2.key"), // timeout expected
            Arguments.of(VALID, "add1.key"),
            Arguments.of(VALID, "bsum1.key"),
            Arguments.of(VALID, "bsum2.key"),
            Arguments.of(UNKNOWN, "bsum3.key"), // timeout expected
            Arguments.of(VALID, "bprod1.key"),
            Arguments.of(VALID, "bprod2.key"),
            Arguments.of(UNKNOWN, "bprod3.key"), // timeout expected
            Arguments.of(UNKNOWN, "binder4.key"), // timeout expected
            Arguments.of(UNKNOWN, "binder5.key"), // timeout expected
            Arguments.of(VALID, "div1.key"),
            Arguments.of(VALID, "div3.key"),
            Arguments.of(UNKNOWN, "div5.key"),
            Arguments.of(UNKNOWN, "div6.key"));
    }
}
