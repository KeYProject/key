/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.script;

import java.io.PrintWriter;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.EngineState;
import de.uka.ilkd.key.scripts.ProofScriptCommand;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultStatus;
import org.key_project.key.cli.prove.OpenGoalPrinter;
import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Interpreter for the line-oriented proof scripts of §7.1 of the headless interface spec.
 * <p>
 * The grammar is {@code proceed | apply <rule-name> [at <position-path>] [for <term>] |
 * auto [<limit>] | assert-closed | print-open-goals}; empty lines and lines starting with
 * {@code #} are ignored. Every executed line is acknowledged on stdout as
 * {@code SCRIPT OK <line>} or {@code SCRIPT FAIL <line> <reason>} (the command text is echoed
 * verbatim, without surrounding whitespace), and {@link #finish()} prints the final marker
 * {@code SCRIPT FINAL closed} or {@code SCRIPT FINAL open <n>}.
 * <p>
 * {@code proceed} and {@code auto} drive the single-threaded KeY strategy
 * ({@link ProofStarter}, {@code setAllowParallel(false)}) with a per-command rule-application cap
 * ({@code proceed} = one step, {@code auto <limit>} = the given limit). {@code apply} resolves the
 * rule name through the regular proof-script engine ({@link ProofScriptEngine},
 * {@link ScriptCommandAst}, {@link ProofScriptCommand}) so the CLI accepts exactly the rule names
 * that interactive KeY accepts.
 * <p>
 * Commands act on the goal designated by the last {@code GOAL} of the preceding
 * {@code print-open-goals}, or on the goal addressed by an {@code at <position-path>} anchor; if no
 * goal was designated yet, the strategy runs on all open goals and {@code apply} uses the first
 * open automatic goal.
 * <p>
 * The {@code print-open-goals} command prints the §6 layout
 * ({@code OPEN-GOAL-COUNT <N>} followed by {@code GOAL <id> <position-path>} blocks) through
 * {@link OpenGoalPrinter}, the same renderer {@code prove --print-open-goals} uses.
 * <p>
 * With a per-command timeout ({@code --timeout}), a strategy command that the timeout cuts short
 * before the proof is closed fails as {@code SCRIPT FAIL <line> timed out after <ms> ms}, and
 * {@link #finish()} then returns exit code {@code 2} (§1: abandoned due to timeout, no decision)
 * while still printing {@code SCRIPT FINAL open <n>}.
 */
public final class ScriptInterpreter {

    /// The stdout prefix of a successfully executed script line.
    public static final String OK_PREFIX = "SCRIPT OK ";

    /// The stdout prefix of a failed script line.
    public static final String FAIL_PREFIX = "SCRIPT FAIL ";

    /// The stdout line printed when the proof is closed at the end of the script.
    public static final String FINAL_CLOSED = "SCRIPT FINAL closed";

    /// The stdout prefix of the final line when goals remain open.
    public static final String FINAL_OPEN_PREFIX = "SCRIPT FINAL open ";

    /// The stdout prefix of the §6 open-goal count line.
    public static final String COUNT_PREFIX = "OPEN-GOAL-COUNT ";

    private static final Logger LOGGER = LoggerFactory.getLogger(ScriptInterpreter.class);

    /**
     * Position path used for the root goal, which has no closing rule application: the root goal
     * exists only in the trivial proof state where it is also the only goal, so {@code 1} can
     * never denote a child node at the same time.
     */
    private static final String ROOT_POSITION = OpenGoalPrinter.ROOT_POSITION;

    private static final String POSITION_PATTERN = "[1-9][0-9]*(\\.[1-9][0-9]*)*";

    private static final String RULE_COMMAND = "rule";

    private final Proof proof;

    private final AbstractUserInterfaceControl uiControl;

    private final long timeoutMs;

    private final PrintWriter out;

    private final ProofScriptEngine engine;

    private final ProofStarter starter;

    private @Nullable Goal selectedGoal;

    private int appliedRuleApplications;

    private long elapsedMs;

    private boolean timedOut;

    /**
     * Creates an interpreter for the given proof.
     *
     * @param proof the proof the script is executed against
     * @param uiControl the user-interface control handed to the proof-script commands
     * @param timeoutMs the per-command proof-search timeout in milliseconds ({@code 0} = none)
     * @param out the writer that receives the {@code SCRIPT ...}, {@code GOAL ...} and
     *        {@code OPEN-GOAL-COUNT ...} lines
     */
    public ScriptInterpreter(Proof proof, AbstractUserInterfaceControl uiControl, long timeoutMs,
            PrintWriter out) {
        this.proof = proof;
        this.uiControl = uiControl;
        this.timeoutMs = Math.max(0, timeoutMs);
        this.out = out;
        this.engine = new ProofScriptEngine(proof);
        this.engine.getStateMap().setEchoOn(false);
        this.starter = new ProofStarter(false);
        this.starter.init(proof);
        this.starter.setAllowParallel(false);
    }

    /**
     * Executes the given script lines in order and prints the final marker.
     *
     * @param lines the script source, one entry per line
     * @return the §1 exit code: {@code 0} if the proof is closed at the end, {@code 2} if it was
     *         abandoned because of the timeout, {@code 1} otherwise
     */
    public int execute(List<String> lines) {
        for (String line : lines) {
            executeLine(line);
        }
        return finish();
    }

    /**
     * Executes a single script line and prints its {@code SCRIPT OK}/{@code SCRIPT FAIL} line.
     * Empty lines and {@code #} comments are ignored (nothing is printed).
     *
     * @param line the raw script line
     * @return {@code true} if the line was executed successfully (or ignored), {@code false} if it
     *         failed
     */
    public boolean executeLine(String line) {
        String command = line.trim();
        if (command.isEmpty() || command.startsWith("#")) {
            return true;
        }
        try {
            run(command);
            out.println(OK_PREFIX + command);
            out.flush();
            return true;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return fail(command, "interrupted");
        } catch (ScriptException e) {
            return fail(command, reason(e));
        } catch (RuntimeException e) {
            LOGGER.debug("Script line '{}' failed unexpectedly", command, e);
            return fail(command, reason(e));
        }
    }

    /**
     * Prints the final marker for the current proof state and returns the exit code.
     *
     * @return the §1 exit code: {@code 0} if the proof is closed, {@code 2} if the search timed
     *         out without closing the proof, {@code 1} if goals remain open
     */
    public int finish() {
        int openGoals = proof.openGoals().size();
        boolean closed = proof.closed() || openGoals == 0;
        out.println(closed ? FINAL_CLOSED : FINAL_OPEN_PREFIX + openGoals);
        out.flush();
        return ExitCode.fromStatus(status()).code();
    }

    /**
     * Returns the final outcome of the script as classified by §1 of the headless interface spec:
     * {@link ResultStatus#CLOSED} if no goal remains open, otherwise
     * {@link ResultStatus#TIMED_OUT} if a strategy command was cut short by the timeout and
     * {@link ResultStatus#OPEN} if the search stopped for any other reason (for example the
     * maximal number of rule applications).
     *
     * @return the status for the §2 {@code KEY_RESULT} record and the §1 exit code
     */
    public ResultStatus status() {
        if (proof.closed() || proof.openGoals().isEmpty()) {
            return ResultStatus.CLOSED;
        }
        return timedOut ? ResultStatus.TIMED_OUT : ResultStatus.OPEN;
    }

    /**
     * Returns the number of rule applications the strategy performed for this script.
     *
     * @return the cumulative number of applied rule applications
     */
    public int appliedRuleApplications() {
        return appliedRuleApplications;
    }

    /**
     * Returns the wall-clock milliseconds the strategy spent for this script.
     *
     * @return the cumulative strategy time in milliseconds
     */
    public long elapsedMs() {
        return elapsedMs;
    }

    private void run(String command) throws ScriptException, InterruptedException {
        String[] tokens = command.split("\\s+");
        switch (tokens[0]) {
            case "proceed" -> {
                requireNoArguments(tokens, command);
                strategy(1);
            }
            case "auto" -> strategy(autoLimit(tokens));
            case "apply" -> apply(tokens);
            case "assert-closed" -> {
                requireNoArguments(tokens, command);
                assertClosed();
            }
            case "print-open-goals" -> {
                requireNoArguments(tokens, command);
                printOpenGoals();
            }
            default -> throw new ScriptException("Unknown command '" + tokens[0] + "'");
        }
    }

    private static void requireNoArguments(String[] tokens, String command)
            throws ScriptException {
        if (tokens.length > 1) {
            throw new ScriptException("Unexpected argument in '" + command + "'");
        }
    }

    /**
     * Returns the step limit for an {@code auto} line: the proof's configured maximal number of
     * steps when no limit is given, otherwise the given non-negative limit.
     */
    private int autoLimit(String[] tokens) throws ScriptException {
        if (tokens.length == 1) {
            return Math.max(1, proof.getSettings().getStrategySettings().getMaxSteps());
        }
        if (tokens.length > 2) {
            throw new ScriptException("Usage: auto [<limit>]");
        }
        try {
            int limit = Integer.parseInt(tokens[1]);
            if (limit < 0) {
                throw new ScriptException("The auto limit must not be negative: " + limit);
            }
            return limit;
        } catch (NumberFormatException e) {
            throw new ScriptException("The auto limit is not an integer: '" + tokens[1] + "'");
        }
    }

    private void apply(String[] tokens) throws ScriptException, InterruptedException {
        if (tokens.length < 2) {
            throw new ScriptException("Usage: apply <rule-name> [at <position-path>] [for <term>]");
        }
        String ruleName = tokens[1];
        @Nullable
        String position = null;
        @Nullable
        String term = null;
        int i = 2;
        while (i < tokens.length) {
            switch (tokens[i]) {
                case "at" -> {
                    if (position != null || i + 1 >= tokens.length) {
                        throw new ScriptException(
                            "Usage: apply <rule-name> [at <position-path>] [for <term>]");
                    }
                    position = tokens[++i];
                }
                case "for" -> {
                    if (term != null || i + 1 >= tokens.length) {
                        throw new ScriptException(
                            "Usage: apply <rule-name> [at <position-path>] [for <term>]");
                    }
                    term = String.join(" ", List.of(tokens).subList(i + 1, tokens.length));
                    i = tokens.length;
                }
                default -> throw new ScriptException("Unexpected token '" + tokens[i] + "'");
            }
            i++;
        }

        @Nullable
        Goal goal = position != null ? goalAt(position) : selectedOpenGoal();
        Map<String, Object> namedArgs = term == null ? Map.of() : Map.of("on", term);
        ScriptCommandAst ast = new ScriptCommandAst(RULE_COMMAND, namedArgs, List.of(ruleName));

        EngineState state = engine.getStateMap();
        state.setGoal(goal);
        ProofScriptCommand command = ProofScriptEngine.getCommand(RULE_COMMAND);
        if (command == null) {
            throw new ScriptException("The 'rule' proof-script command is not available");
        }
        command.execute(uiControl, ast, state);
        if (goal != null && goal.node().isClosed()) {
            selectedGoal = null;
        }
    }

    private void assertClosed() throws ScriptException {
        int openGoals = proof.openGoals().size();
        if (!proof.closed() && openGoals > 0) {
            throw new ScriptException("proof is not closed (" + openGoals + " open goals)");
        }
    }

    private void strategy(int maxSteps) throws ScriptException {
        ImmutableList<Goal> goals = targetGoals();
        if (goals.isEmpty()) {
            throw new ScriptException("proof is already closed");
        }
        starter.setMaxRuleApplications(maxSteps);
        starter.setTimeout(timeoutMs > 0 ? timeoutMs : -1L);
        ProofSearchInformation<Proof, Goal> info = starter.start(goals);
        appliedRuleApplications += info.getNumberOfAppliedRuleApps();
        elapsedMs += info.getTime();
        if (selectedGoal != null && selectedGoal.node().isClosed()) {
            selectedGoal = null;
        }
        if (timeoutMs > 0 && !proof.closed() && info.getTime() >= timeoutMs) {
            timedOut = true;
            throw new ScriptException("timed out after " + info.getTime() + " ms");
        }
    }

    /**
     * Returns the goals a strategy command acts on: the goal designated by the last
     * {@code print-open-goals} if it is still open, otherwise all open goals.
     */
    private ImmutableList<Goal> targetGoals() {
        Goal goal = selectedOpenGoal();
        return goal != null ? ImmutableList.of(goal) : proof.openGoals();
    }

    private @Nullable Goal selectedOpenGoal() {
        if (selectedGoal != null && selectedGoal.node().isClosed()) {
            selectedGoal = null;
        }
        return selectedGoal;
    }

    /**
     * Resolves a §6 position path against the current proof.
     *
     * @param position the dot-separated child indices (1-based), as printed by
     *        {@code print-open-goals}
     * @return the open goal at that position
     * @throws ScriptException if the path is malformed, does not exist or is not an open goal
     */
    private Goal goalAt(String position) throws ScriptException {
        if (!position.matches(POSITION_PATTERN)) {
            throw new ScriptException("Invalid position path '" + position + "'");
        }
        Node node;
        if (ROOT_POSITION.equals(position) && proof.root().childrenCount() == 0) {
            node = proof.root();
        } else {
            node = proof.root();
            for (String step : position.split("\\.")) {
                int child = Integer.parseInt(step) - 1;
                if (child < 0 || child >= node.childrenCount()) {
                    throw new ScriptException("No node at position path '" + position + "'");
                }
                node = node.child(child);
            }
        }
        for (Goal goal : proof.openGoals()) {
            if (goal.node() == node) {
                return goal;
            }
        }
        throw new ScriptException("No open goal at position path '" + position + "'");
    }

    /**
     * Prints the §6 open-goal layout for the current proof state and designates the last printed
     * goal as the target of the following commands. The layout is rendered by
     * {@link OpenGoalPrinter}, so {@code script print-open-goals} is byte-identical to
     * {@code prove --print-open-goals 0}.
     */
    private void printOpenGoals() {
        new OpenGoalPrinter(out, 0, true).print(proof);
        ImmutableList<Goal> goals = proof.openGoals();
        selectedGoal = goals.isEmpty() ? null : goals.get(goals.size() - 1);
    }

    private boolean fail(String command, String reason) {
        out.println(FAIL_PREFIX + command + " " + reason);
        out.flush();
        return false;
    }

    private static String reason(Exception e) {
        String message = e.getMessage();
        return message != null && !message.isBlank() ? message : e.getClass().getSimpleName();
    }
}
