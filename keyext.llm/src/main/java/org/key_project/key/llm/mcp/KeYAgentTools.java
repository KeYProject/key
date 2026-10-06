/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;

import org.key_project.key.llm.FileAccess;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.ProofContextCollector;
import org.key_project.key.llm.ShellSafetyPolicy;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

import static org.key_project.key.llm.mcp.Tool.ApprovalRequirement.ASK;
import static org.key_project.key.llm.mcp.Tool.ApprovalRequirement.AUTO;

/**
 * The built-in tool set of the KeY-Agent:
 * <ul>
 * <li>{@code get_proof_context} - the current proof state as a text block</li>
 * <li>{@code list_files} / {@code read_file} / {@code file_info} - bounded, sandboxed access to
 * the files of the current Java model</li>
 * <li>{@code run_command} - executes a shell command in the model directory (blocklist + user
 * approval required)</li>
 * <li>{@code ask_user} - asks the user a question (intercepted by the agent loop)</li>
 * <li>{@code tryclose} - applies the {@code tryclose} proof-script command (TryClose macro) to a
 * goal, a branch or all open goals</li>
 * <li>{@code auto} - applies KeY's automatic proof strategy with a given step limit
 * (the {@code auto} proof-script command)</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class KeYAgentTools implements McpClient {

    public static final String TOOL_GET_PROOF_CONTEXT = "get_proof_context";
    public static final String TOOL_LIST_FILES = "list_files";
    public static final String TOOL_READ_FILE = "read_file";
    public static final String TOOL_FILE_INFO = "file_info";
    public static final String TOOL_RUN_COMMAND = "run_command";
    public static final String TOOL_ASK_USER = "ask_user";
    public static final String TOOL_USE_SKILL = "use_skill";
    public static final String TOOL_TRYCLOSE = "tryclose";
    public static final String TOOL_AUTO = "auto";

    private final ShellSafetyPolicy safetyPolicy = new ShellSafetyPolicy();

    private static @Nullable Proof selectedProof() {
        var mediator = MainWindow.getInstance().getMediator();
        return mediator == null ? null : mediator.getSelectedProof();
    }

    @Override
    public List<Tool> getTools() {
        return List.of(
            tool(TOOL_GET_PROOF_CONTEXT, "Returns a text block describing the current proof state:"
                + " name, open/closed goals, the current sequent, open goal sequents, model info and"
                + " the computation path from the root to the selected node.", AUTO,
                schema(
                    "include_compute_path",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("include the computation path")
                            .build())),
            tool(TOOL_LIST_FILES, "Lists files of the current Java model directory (relative paths,"
                + " bounded). Use with an optional prefix to filter.", AUTO,
                schema("prefix",
                    JsonSchema.builder().withType("string")
                            .withDescription("optional path prefix to filter").build())),
            tool(TOOL_READ_FILE, "Reads a text file of the current Java model directory (relative"
                + " path). Respects the configured size limits.", AUTO,
                schema("path",
                    JsonSchema.builder().withType("string")
                            .withDescription("relative path inside the model")
                            .build())),
            tool(TOOL_FILE_INFO, "Returns metadata (size, last modified, kind) of a file inside the"
                + " model directory.", AUTO,
                schema("path",
                    JsonSchema.builder().withType("string")
                            .withDescription("relative path inside the model")
                            .build())),
            tool(TOOL_RUN_COMMAND, "Runs a shell command in the model directory. Requires user"
                + " approval. Destructive commands are blocked by a blocklist.", ASK,
                schema(
                    "command", JsonSchema.builder().withType("string")
                            .withDescription("the shell command to run").build())),
            tool(TOOL_ASK_USER, "Asks the user a question. Use this whenever a case split, an"
                + " assumption or a design decision is ambiguous. The user's answer is returned"
                + " verbatim.", AUTO,
                schema("question",
                    JsonSchema.builder().withType("string").withDescription("the question text")
                            .build(),
                    "options",
                    JsonSchema.builder().withType("array")
                            .withDescription("optional answer options")
                            .withItems(JsonSchema.builder().withType("string").build()).build())),
            tool(TOOL_USE_SKILL, "Activates a user-defined skill by name. Skills add focused"
                + " instructions to the system prompt of this and subsequent turns. Enabled only"
                + " when the 'agent can use skills' setting is on.", AUTO,
                schema("name",
                    JsonSchema.builder().withType("string")
                            .withDescription("the name of the skill to activate").build())),
            tool(TOOL_TRYCLOSE, "Applies the KeY proof-script command 'tryclose' to the current"
                + " proof: it automatically tries to close goals with the TryClose strategy."
                + " Targets either the first open goal of the current branch (default), all open"
                + " goals, or a single goal by index.", AUTO,
                schema(
                    "branch",
                    JsonSchema.builder().withType("string")
                            .withDescription("the target: \"branch\" (first open goal, default),"
                                + " \"all\" (all open goals), or the 0-based index of one open"
                                + " goal")
                            .build(),
                    "steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps")
                            .build(),
                    "assertClosed",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("report an error if the target cannot be closed")
                            .build())),
            tool(TOOL_AUTO, "Applies KeY's automatic proof strategy (the 'Auto' button / the"
                + " 'auto' proof-script command) to the current branch, with an arbitrary maximum"
                + " number of proof steps. Use it to try to discharge the current goal by"
                + " automatic proof search.", AUTO,
                schema(
                    "steps",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of proof steps (the configured"
                                + " strategy limit applies if omitted)")
                            .build(),
                    "all",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("apply the strategy to all open goals instead of the"
                                + " first one")
                            .build())));
    }

    private static Tool tool(String name, String description, Tool.ApprovalRequirement approval,
            JsonSchema parameters) {
        return new Tool(new FunctionDefinition(name, description, parameters), approval);
    }

    private static JsonSchema schema(Object... keyValue) {
        var builder = JsonSchema.builder().withType("object");
        for (int i = 0; i + 1 < keyValue.length; i += 2) {
            builder.addProperty((String) keyValue[i], (JsonSchema) keyValue[i + 1]);
        }
        return builder.build();
    }

    @SuppressWarnings("unchecked")
    @Override
    public Object callTool(String toolName, String arguments) throws Exception {
        var args = parseArgs(arguments);
        return switch (toolName) {
            case TOOL_GET_PROOF_CONTEXT -> contextBlock(args);
            case TOOL_LIST_FILES -> listFiles(stringArg(args, "prefix"));
            case TOOL_READ_FILE -> readFile(stringArg(args, "path"), false);
            case TOOL_FILE_INFO -> readFile(stringArg(args, "path"), true);
            case TOOL_RUN_COMMAND -> runCommand(stringArg(args, "command"));
            case TOOL_ASK_USER ->
                "[ask_user is interactive and handled by the agent loop; it cannot be called "
                    + "directly]";
            case TOOL_USE_SKILL ->
                "[use_skill is handled by the agent loop; it cannot be called directly]";
            case TOOL_TRYCLOSE -> tryClose(args);
            case TOOL_AUTO -> runAuto(args);
            default -> throw new IllegalArgumentException("unknown tool: " + toolName);
        };
    }

    private static Map<String, Object> parseArgs(String arguments) {
        if (arguments == null || arguments.isBlank()) {
            return Map.of();
        }
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Map.class);
            return parsed == null ? Map.of() : parsed;
        } catch (Exception e) {
            return Map.of();
        }
    }

    private static @Nullable String stringArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        return v == null ? null : String.valueOf(v);
    }

    private static boolean boolArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        return v instanceof Boolean b && b || "true".equals(v);
    }

    private static @Nullable Integer intArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        if (v instanceof Number n) {
            return n.intValue();
        }
        if (v != null) {
            try {
                return Integer.parseInt(String.valueOf(v).trim());
            } catch (NumberFormatException e) {
                return null;
            }
        }
        return null;
    }

    // ----------------------------------------------------------------- proof-manipulation tools

    /**
     * Runs the {@code tryclose} proof-script command. The default target is the first open goal
     * (mirroring {@code tryclose branch;}); {@code "all"} or a goal index select the other
     * targets.
     */
    private static String tryClose(Map<String, Object> args) {
        return runScript(tryCloseCommand(stringArg(args, "branch"), intArg(args, "steps"),
            boolArg(args, "assertClosed")));
    }

    /** Runs the {@code auto} proof-script command with the given step limit. */
    private static String runAuto(Map<String, Object> args) {
        return runScript(autoCommand(intArg(args, "steps"), boolArg(args, "all")));
    }

    /**
     * Builds the {@code tryclose} script command from the tool parameters. {@code null}/{@code
     * blank}/{@code "branch"} targets the first open goal, {@code "all"} all open goals, and a
     * decimal string the goal with that index.
     */
    static ScriptCommandAst tryCloseCommand(@Nullable String branch, @Nullable Integer steps,
            boolean assertClosed) {
        List<Object> positional;
        if (branch == null || branch.isBlank() || "branch".equals(branch)) {
            positional = List.of("branch");
        } else if ("all".equals(branch)) {
            positional = List.of();
        } else {
            try {
                Integer.parseInt(branch);
                positional = List.of(branch);
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException(
                    "'branch' must be \"branch\", \"all\" or a goal index, got: " + branch);
            }
        }

        var named = new HashMap<String, Object>();
        if (steps != null) {
            named.put("steps", steps);
        }
        if (assertClosed) {
            named.put("assertClosed", true);
        }
        return new ScriptCommandAst("tryclose", named, positional);
    }

    /** Builds the {@code auto} script command from the tool parameters. */
    static ScriptCommandAst autoCommand(@Nullable Integer steps, boolean all) {
        var named = new HashMap<String, Object>();
        if (steps != null) {
            named.put("steps", steps);
        }
        if (all) {
            named.put("all", true);
        }
        return new ScriptCommandAst("auto", named, List.of());
    }

    /**
     * Executes a single proof-script command on the currently selected proof via the
     * {@link ProofScriptEngine}, i.e. through the same machinery as the "Apply Script" action.
     * The result tells the agent how many open goals remain.
     */
    private static String runScript(ScriptCommandAst command) {
        var proof = selectedProof();
        if (proof == null) {
            return "Error: no proof selected";
        }
        int before = proof.openGoals().size();
        var ui = MainWindow.getInstance().getMediator().getUI();
        try {
            new ProofScriptEngine(proof).execute(ui, List.of(command));
        } catch (ScriptException e) {
            return "Error: " + e.getMessage();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "Error: proof search interrupted";
        }
        int after = proof.openGoals().size();
        int closed = before - after;
        return command.commandName() + ": " + closed + " goal(s) closed, " + after
            + " open goal(s) remain" + (after == 0 ? " - the proof is closed" : "") + ".";
    }

    private static String contextBlock(Map<String, Object> args) {
        var proof = selectedProof();
        if (proof == null) {
            return "(no proof selected)";
        }
        var node = MainWindow.getInstance().getMediator().getSelectedNode();
        return ProofContextCollector.contextBlock(proof, node);
    }

    private static String listFiles(@Nullable String prefix) {
        var proof = selectedProof();
        var files = FileAccess.listFiles(proof);
        var filtered = prefix == null || prefix.isBlank() ? files
                : files.stream().filter(p -> {
                    var rel = FileAccess.relativeName(proof, p);
                    return rel != null && rel.startsWith(prefix);
                }).toList();
        if (filtered.isEmpty()) {
            return "(no files" + (prefix == null ? "" : " matching prefix \"" + prefix + "\"")
                + ")";
        }
        return filtered.stream().map(p -> {
            var rel = FileAccess.relativeName(proof, p);
            return "- " + (rel == null ? p : rel);
        }).collect(Collectors.joining("\n"));
    }

    private static String readFile(@Nullable String path, boolean info) {
        if (path == null || path.isBlank()) {
            return "Error: 'path' parameter is required";
        }
        var proof = selectedProof();
        if (proof == null) {
            return "Error: no proof selected; no model directory available";
        }
        var resolved = FileAccess.resolveInModel(proof, path);
        if (resolved == null || !Files.exists(resolved)) {
            return "Error: file not found inside the model directory: " + path;
        }
        if (FileAccess.isBinary(path)) {
            return "Error: binary file (not offered for reading): " + path;
        }
        if (info) {
            try {
                return "path: " + path + "\nsize: " + Files.size(resolved)
                    + " bytes\nlast modified: "
                    + Files.getLastModifiedTime(resolved) + "\nregular file: "
                    + Files.isRegularFile(resolved);
            } catch (IOException e) {
                return "Error: " + e.getMessage();
            }
        }
        try {
            return FileAccess.readText(resolved);
        } catch (IOException e) {
            return "Error: " + e.getMessage();
        }
    }

    private String runCommand(@Nullable String command) throws Exception {
        if (command == null || command.isBlank()) {
            return "Error: 'command' parameter is required";
        }
        var settings = LlmSettings.INSTANCE;
        var verdict = safetyPolicy.evaluate(command);
        if (!verdict.allowed()) {
            return "[Command blocked by safety policy: " + verdict.reason() + "]";
        }
        if (!settings.getShellEnabled()) {
            return "[Shell commands are disabled in the LLM settings]";
        }
        var proof = selectedProof();
        var workDir = proof == null ? null : FileAccess.modelRoot(proof);
        var pb = new ProcessBuilder("/bin/sh", "-c", command);
        pb.redirectErrorStream(true);
        if (workDir != null) {
            pb.directory(workDir.toFile());
        }
        Process process;
        try {
            process = pb.start();
        } catch (IOException e) {
            return "Error: could not start command: " + e.getMessage();
        }
        int timeout = Math.max(1, settings.getShellTimeoutSeconds());
        int maxChars = Math.max(1, settings.getShellMaxOutputChars());

        var outFuture = CompletableFuture.supplyAsync(
            () -> readBounded(process.getInputStream(), maxChars));
        boolean done;
        try {
            done = process.waitFor(timeout, TimeUnit.SECONDS);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            process.destroyForcibly();
            return "Error: interrupted";
        }
        if (!done) {
            process.destroyForcibly();
            return "[Command timed out after " + timeout + "s and was terminated]";
        }
        try {
            String output = outFuture.get(2, TimeUnit.SECONDS);
            return "exit code: " + process.exitValue() + "\n" + output;
        } catch (Exception e) {
            return "exit code: " + process.exitValue() + "\n(output unavailable)";
        }
    }

    private static String readBounded(InputStream in, int maxChars) {
        var sb = new StringBuilder();
        byte[] buf = new byte[4096];
        try {
            int read;
            while ((read = in.read(buf)) != -1 && sb.length() < maxChars) {
                int keep = Math.min(read, maxChars - sb.length());
                sb.append(new String(buf, 0, keep, StandardCharsets.UTF_8));
            }
        } catch (IOException e) {
            // stream closed (e.g. command terminated early)
        }
        if (sb.length() >= maxChars) {
            sb.append("\n... [output truncated]");
        }
        return sb.toString();
    }

    @Override
    public boolean isClosed() {
        return false;
    }

    @Override
    public void close() {
    }
}
