/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.script;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.prove.ContractIndex;
import org.key_project.key.cli.prove.Fixtures;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@link ScriptInterpreter} in isolation (no command-line parsing).
 */
class ScriptInterpreterTest {

    private static final String SIZE_NAME =
        "Size[Size::size(int)].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(600)
    void autoHonoursTheStepLimit() throws Exception {
        StringWriter out = new StringWriter();
        try (KeYEnvironment<DefaultUserInterfaceControl> env = loadSize()) {
            Proof proof = createProof(env);
            try {
                ScriptInterpreter interpreter = interpreter(proof, env, out);

                assertThat(interpreter.executeLine("auto 5")).isTrue();

                assertThat(interpreter.appliedRuleApplications()).isBetween(1, 5);
                assertThat(proof.closed()).isFalse();
            } finally {
                proof.dispose();
            }
        }
    }

    @Test
    @Timeout(600)
    void printOpenGoalsOnFreshProofPrintsTheRootPositionPath() throws Exception {
        StringWriter out = new StringWriter();
        try (KeYEnvironment<DefaultUserInterfaceControl> env = loadSize()) {
            Proof proof = createProof(env);
            try {
                ScriptInterpreter interpreter = interpreter(proof, env, out);

                assertThat(interpreter.executeLine("print-open-goals")).isTrue();

                List<String> goalLines = out.toString().lines()
                        .filter(line -> line.startsWith("GOAL ")).toList();
                assertThat(goalLines).isNotEmpty();
                assertThat(goalLines.get(0)).isEqualTo("GOAL 0 1");
                assertThat(goalLines)
                        .allMatch(line -> line.matches("GOAL [0-9]+ [1-9][0-9.]*"));
            } finally {
                proof.dispose();
            }
        }
    }

    @Test
    @Timeout(600)
    void applyResolvesThePositionPathPrintedByPrintOpenGoals() throws Exception {
        StringWriter out = new StringWriter();
        try (KeYEnvironment<DefaultUserInterfaceControl> env = loadSize()) {
            Proof proof = createProof(env);
            try {
                ScriptInterpreter interpreter = interpreter(proof, env, out);

                assertThat(interpreter.executeLine("proceed")).isTrue();
                assertThat(interpreter.executeLine("print-open-goals")).isTrue();

                String path = lastGoalPath(out.toString());
                assertThat(path).matches("[1-9][0-9.]*");

                assertThat(interpreter.executeLine("apply impRight at " + path))
                        .as(out.toString())
                        .isTrue();
                assertThat(out.toString()).contains("SCRIPT OK apply impRight at " + path);
                // without an `at` anchor the rule applies to the last goal shown
                assertThat(interpreter.executeLine("apply andLeft")).as(out.toString()).isTrue();
            } finally {
                proof.dispose();
            }
        }
    }

    private static ScriptInterpreter interpreter(Proof proof,
            KeYEnvironment<DefaultUserInterfaceControl> env, StringWriter out) {
        return new ScriptInterpreter(proof, env.getUi(), 0, new PrintWriter(out));
    }

    private static KeYEnvironment<DefaultUserInterfaceControl> loadSize() throws Exception {
        return KeYEnvironment.load(Fixtures.resource("/fixtures/size/size.key"));
    }

    private static Proof createProof(KeYEnvironment<DefaultUserInterfaceControl> env)
            throws Exception {
        Contract contract = ContractIndex.fromEnvironment(env).byName(SIZE_NAME).orElseThrow();
        return env.createProof(contract.createProofObl(env.getInitConfig()));
    }

    private static String lastGoalPath(String out) {
        return out.lines().filter(line -> line.startsWith("GOAL "))
                .reduce((first, second) -> second).orElseThrow().split(" ")[2];
    }
}
