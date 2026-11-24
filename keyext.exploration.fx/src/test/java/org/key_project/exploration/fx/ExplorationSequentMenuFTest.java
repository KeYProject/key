/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless (toolkit-free) unit test of the {@code promptForTerm} retry-loop of
 * {@link ExplorationSequentMenuF} (WP-5, the port of the Swing
 * {@code ExplorationAction.promptForTerm} modal retry-loop, ExplorationAction.java:35-65): a
 * malformed input and a sort mismatch must re-open the input (the Swing parity) instead of
 * aborting, and cancelling must abort the action.
 * <p>
 * Like {@code KeYMediatorFSeamsTest} the tests run against a real proof of the standard JavaDL
 * profile loaded headlessly via {@link KeYEnvironment}; the loop is driven through the
 * {@link ExplorationSequentMenuF.PromptHandler} seam (the dialog handler is only used in the
 * running app), so no JavaFX toolkit and no dialogs are involved.
 */
class ExplorationSequentMenuFTest {

    /** A scripted handler: feeds the queued inputs and records the shown errors. */
    private static final class ScriptedPrompt implements ExplorationSequentMenuF.PromptHandler {
        final List<String> inputs;
        final List<String> errorTitles = new ArrayList<>();
        final List<String> errorMessages = new ArrayList<>();
        int next;

        ScriptedPrompt(String... inputs) {
            this.inputs = List.of(inputs);
        }

        @Override
        public String input(String initialValue, String errorTitle, String errorMessage) {
            if (errorTitle != null) {
                errorTitles.add(errorTitle);
                errorMessages.add(errorMessage);
            }
            return next < inputs.size() ? inputs.get(next++) : null;
        }
    }

    private KeYEnvironment<?> env;
    private Goal goal;

    @BeforeEach
    void loadProof() throws Exception {
        Path dir = Files.createTempDirectory("exploration-prompt");
        Path main = dir.resolve("test.key");
        // No \include: the JavaDL profile loads the standard library from the classpath.
        Files.writeString(main, "\\problem { true }\n");
        env = KeYEnvironment.load(main);
        Proof proof = env.getLoadedProof();
        goal = proof.openGoals().head();
    }

    @AfterEach
    void unloadProof() {
        if (env != null) {
            env.dispose();
        }
    }

    @Test
    void retryAcceptsBadThenGoodInput() {
        // malformed input ("(((") shows the "Malformed input" error and re-prompts; the good
        // input is then accepted (Swing ExplorationAction.java:54-57)
        ScriptedPrompt prompt = new ScriptedPrompt("(((", "true");
        JTerm result = ExplorationSequentMenuF.promptForTerm(goal, null, prompt);
        assertNotNull(result);
        assertEquals(List.of("Malformed input"), prompt.errorTitles);
        assertEquals(2, prompt.next);
    }

    @Test
    void retryAfterSortMismatch() throws Exception {
        KeyIO io = new KeyIO(goal.proof().getServices());
        JTerm intTerm = io.parseExpression("0");
        // the first input is a formula (wrong sort): the "Sort mismatch" error re-prompts and the
        // matching int literal is accepted (Swing ExplorationAction.java:46-53)
        ScriptedPrompt prompt = new ScriptedPrompt("true", "1");
        JTerm result = ExplorationSequentMenuF.promptForTerm(goal, intTerm, prompt);
        assertNotNull(result);
        assertEquals(intTerm.sort(), result.sort());
        assertEquals(List.of("Sort mismatch"), prompt.errorTitles);
        assertTrue(prompt.errorMessages.get(0).contains("sort"));
    }

    @Test
    void cancelAbortsTheAction() {
        ScriptedPrompt prompt = new ScriptedPrompt();
        assertNull(ExplorationSequentMenuF.promptForTerm(goal, null, prompt));
        assertTrue(prompt.errorTitles.isEmpty());
    }

    @Test
    void goodInputIsAcceptedOnTheFirstAsk() {
        ScriptedPrompt prompt = new ScriptedPrompt("true");
        JTerm result = ExplorationSequentMenuF.promptForTerm(goal, null, prompt);
        assertNotNull(result);
        assertTrue(prompt.errorTitles.isEmpty());
    }
}
