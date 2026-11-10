/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.key_project.key.llm.LlmSession;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.ToolFacade;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import jdk.jshell.Diag;
import jdk.jshell.JShell;
import jdk.jshell.Snippet;
import jdk.jshell.SnippetEvent;

/**
 * The {@code execute} tool: evaluates a Java snippet in an embedded in-process JShell. The
 * snippet reaches the agent's tools through the {@code tools} facade (a
 * {@link ToolFacade} variable bound by the preamble); the call is intercepted by the agent
 * loop and dispatched <em>outside</em> the global dispatch lock, because the facade's own
 * tool calls acquire that lock (holding it across the whole snippet would deadlock).
 * <p>
 * By default the snippet runs with a best-effort safety gate that rejects the obvious escape
 * hatches (process spawning, exiting the JVM, reflection, raw file and network I/O) and steers
 * snippets to the facade; the <em>Unrestricted execute</em> setting switches the gate off
 * (full JVM and classpath access). There is no true confinement in-process - approval is the
 * real gate; every call asks the user (ASK requirement).
 * <p>
 * Output is bounded: the values of the evaluated expression snippets are returned, capped at
 * {@code executeMaxOutputChars}; a snippet exceeding {@code executeTimeoutSeconds} is stopped
 * (best effort) and reported as timed out.
 *
 * @author Alexander Weigl
 */
public final class ScriptingTools implements AgentToolProvider {

    /**
     * Tokens the safety gate rejects in the restricted mode (best effort: the approval
     * requirement, not this list, is the security boundary).
     */
    static final List<String> RESTRICTED_TOKENS = List.of(
        "System.exit", "System.load", "System.loadLibrary", "System.setSecurityManager",
        "Runtime.", "ProcessBuilder", "Class.forName", "ClassLoader", "java.lang.reflect",
        "MethodHandles", "sun.misc.Unsafe", "java.nio.file", "java.io.File",
        "java.io.FileInputStream", "java.io.FileOutputStream", "java.io.RandomAccessFile",
        "java.net.", "java.sql.", "javax.naming", "jdk.jshell");

    /** The preamble template binding the {@code tools} facade variable (formatted with the key). */
    static final String PREAMBLE_TEMPLATE =
        "var tools = org.key_project.key.llm.ToolFacade.byKey(\"%s\");%n";

    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_EXECUTE, ToolCategory.SCRIPTING,
            "Evaluates a Java snippet in an embedded JShell and returns the values of the"
                + " evaluated expressions (bounded). The snippet has a variable `tools`"
                + " (org.key_project.key.llm.ToolFacade) with methods for the standard tools:"
                + " tools.glob(pattern), tools.read(path[, offset[, limit]]), tools.grep"
                + " (pattern[, include]), tools.write(path, content), tools.edit(path,"
                + " oldString, newString), tools.shell(command), tools.webfetch(url),"
                + " tools.websearch(query), tools.listTools() and tools.call(name, arguments)"
                + " for every registered tool. Java 21 syntax, no imports needed for tools."
                + " By default a safety gate rejects snippets that spawn processes, exit the"
                + " JVM, use reflection or raw file/network I/O; the 'Unrestricted execute'"
                + " setting switches the gate off. The script was approved as a whole:"
                + " facade calls do not ask again. A snippet may not ask the user questions.",
            Tool.ApprovalRequirement.ASK,
            JsonSchema.builder().withType("object")
                    .addProperty("code",
                        JsonSchema.builder().withType("string")
                                .withDescription("the Java snippet to evaluate; end with the"
                                    + " expression whose value is the answer")
                                .build())
                    .withRequired(List.of("code"))
                    .build(),
            true,
            args -> "[execute is handled by the agent loop; it cannot be called directly]"));
    }

    // ------------------------------------------------------------------------ execution

    /**
     * Runs the {@code execute} tool call: parses {@code code}, applies the safety gate, runs
     * the snippet in a fresh JShell with the {@code tools} facade bound, and returns the
     * stringified result. Called by the agent loop on a dispatcher thread without the dispatch
     * lock (the facade's own calls acquire it per call).
     */
    public static String run(LlmSession session, String arguments) {
        var args = AgentTool.parseArgs(arguments);
        var code = AgentTool.stringArg(args, "code");
        if (code == null || code.isBlank()) {
            return "Error: 'code' parameter is required";
        }
        var settings = LlmSettings.INSTANCE;
        if (!settings.getUnrestrictedExecute()) {
            var violation = restrictedToken(code);
            if (violation != null) {
                return "[Script rejected by the safety gate: the snippet uses \"" + violation
                    + "\". Rewrite it with the tools facade (variable `tools`), or enable"
                    + " 'Unrestricted execute' in the LLM settings if you really want raw"
                    + " JVM access.]";
            }
        }
        var facade = new ToolFacade(session);
        return eval(code, facade, settings.getExecuteTimeoutSeconds(),
            settings.getExecuteMaxOutputChars());
    }

    /**
     * Evaluates {@code code} in a fresh in-process JShell with {@code facade} bound as the
     * {@code tools} variable (published under a fresh registry key for the preamble). The code
     * is split into statements (like the JShell REPL does) so every statement's value is
     * captured. Package-private so the semantics can be tested headless.
     */
    static String eval(String code, ToolFacade facade, int timeoutSeconds, int maxOutputChars) {
        var key = java.util.UUID.randomUUID().toString();
        ToolFacade.register(key, facade);
        try {
            var shell = newShell();
            var preamble = String.format(PREAMBLE_TEMPLATE, key);
            var preambleEvents = shell.eval(preamble);
            if (!preambleEvents.isEmpty()
                    && preambleEvents.get(preambleEvents.size() - 1)
                            .status() == Snippet.Status.REJECTED) {
                var preambleError = report(shell, preambleEvents);
                shell.close();
                return "Error: could not bind the tools facade: " + preambleError;
            }
            var outcome = evaluate(shell, code, timeoutSeconds);
            if (outcome.abandoned()) {
                // the snippet may still be running: the shell is abandoned, not closed
                // (closing could block on the stopped evaluation)
                return outcome.errorText();
            }
            var result = outcome.errorText() != null ? outcome.errorText()
                    : report(shell, outcome.events());
            shell.close();
            if (result.length() > maxOutputChars) {
                result = result.substring(0, maxOutputChars) + "\n... [output truncated at "
                    + maxOutputChars + " characters]";
            }
            return result.isBlank()
                    ? "(no result; end the snippet with the expression whose value you want"
                        + " returned)"
                    : result;
        } finally {
            ToolFacade.unregister(key);
        }
    }

    /**
     * One evaluation result: the snippet events, a pre-formatted error text (or {@code null}),
     * and whether the JShell was abandoned because a snippet may still be running.
     */
    private record EvalOutcome(List<SnippetEvent> events, String errorText, boolean abandoned) {
    }

    /**
     * Evaluates the statements of {@code code} one by one (the JShell REPL's own splitting via
     * {@link jdk.jshell.SourceCodeAnalysis#analyzeCompletion(String)}), all within the timeout.
     */
    private static EvalOutcome evaluate(JShell shell, String code, int timeoutSeconds) {
        var executor = Executors.newSingleThreadExecutor(r -> {
            var thread = new Thread(r, "key-execute-jshell");
            thread.setDaemon(true);
            return thread;
        });
        try {
            Future<EvalOutcome> future = executor.submit(() -> {
                var analysis = shell.sourceCodeAnalysis();
                var events = new ArrayList<SnippetEvent>();
                var remaining = code.strip();
                while (!remaining.isEmpty()) {
                    var info = analysis.analyzeCompletion(remaining);
                    if (info.source().isEmpty()) {
                        if (info.completeness() == jdk.jshell.SourceCodeAnalysis.Completeness.DEFINITELY_INCOMPLETE) {
                            return new EvalOutcome(List.copyOf(events),
                                "Error: the snippet is incomplete (unclosed brace or quote?): "
                                    + lastLine(remaining.strip()),
                                false);
                        }
                        break;
                    }
                    events.addAll(shell.eval(info.source()));
                    var next = info.remaining().strip();
                    if (next.equals(remaining)) {
                        break; // cannot make progress (defensive)
                    }
                    remaining = next;
                }
                return new EvalOutcome(List.copyOf(events), null, false);
            });
            try {
                return future.get(Math.max(1, timeoutSeconds), TimeUnit.SECONDS);
            } catch (TimeoutException e) {
                // abandon the shell (closing could block on the still-running snippet)
                stop(shell);
                return new EvalOutcome(List.of(),
                    "[Script timed out after " + Math.max(1, timeoutSeconds)
                        + " s and was stopped. Split long-running work into smaller snippets or"
                        + " run it with tools.shell(command).]",
                    true);
            } catch (Exception e) {
                var cause = e.getCause() == null ? e : e.getCause();
                return new EvalOutcome(List.of(),
                    "Error: snippet evaluation failed: " + cause.getMessage(), false);
            } finally {
                executor.shutdownNow();
            }
        } finally {
            executor.shutdownNow();
        }
    }

    /** The last line of a source text (for error excerpts). */
    private static String lastLine(String source) {
        var index = source.lastIndexOf('\n');
        return index < 0 ? source : source.substring(index + 1);
    }

    /** Creates an in-process JShell (snippets run on an engine thread, no child JVM). */
    private static JShell newShell() {
        return JShell.builder()
                .executionEngine(new jdk.jshell.execution.LocalExecutionControlProvider(), Map.of())
                .build();
    }

    /** Best-effort stop of a running evaluation (unsupported engines are ignored). */
    private static void stop(JShell shell) {
        try {
            shell.stop();
        } catch (RuntimeException ignored) {
            // the engine may not support stopping; the snippet thread is abandoned
        }
    }

    /**
     * Formats the snippet events: the value of every evaluated expression (method-call
     * expressions and the temporary variables JShell creates for bare expressions), the
     * compiler diagnostics of rejected snippets, and snippet exceptions. The initializers of
     * user-declared variables are not echoed. Package-private for tests.
     */
    static String report(JShell shell, List<SnippetEvent> events) {
        var values = new ArrayList<String>();
        var errors = new ArrayList<String>();
        for (var event : events) {
            if (event.status() == Snippet.Status.REJECTED) {
                var message = shell.diagnostics(event.snippet()).map(d -> message(d)).findFirst()
                        .orElse("syntax error");
                errors.add("Error: rejected snippet (" + message + "): "
                    + event.snippet().source().strip());
                continue;
            }
            if (event.exception() != null) {
                errors.add("Error: " + event.exception().getMessage());
                continue;
            }
            if (event.value() != null && isExpressionResult(event.snippet())) {
                values.add(event.value());
            }
        }
        var result = String.join("\n", values);
        if (!errors.isEmpty()) {
            result = result.isBlank() ? String.join("\n", errors)
                    : result + "\n" + String.join("\n", errors);
        }
        return result;
    }

    /**
     * Whether the snippet's value is the result of an evaluated expression: a method-call or
     * assignment expression, or one of the temporary variables JShell creates for bare
     * expressions (their names start with {@code $}). User-declared variables are skipped.
     */
    private static boolean isExpressionResult(Snippet snippet) {
        if (snippet instanceof jdk.jshell.ExpressionSnippet) {
            return true;
        }
        return snippet instanceof jdk.jshell.VarSnippet var
                && var.name().startsWith("$");
    }

    /** A readable compiler message of a JShell diagnostic. */
    private static String message(Diag diagnostic) {
        var text = diagnostic.getMessage(null);
        return text == null ? "diagnostic" : text.strip();
    }

    /**
     * The first restricted token used by {@code code}, or {@code null} if none (the snippet
     * passes the safety gate). Package-private for tests.
     */
    static String restrictedToken(String code) {
        for (var token : RESTRICTED_TOKENS) {
            if (code.contains(token)) {
                return token;
            }
        }
        return null;
    }
}
