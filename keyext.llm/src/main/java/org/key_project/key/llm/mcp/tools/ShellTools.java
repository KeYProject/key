/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import org.key_project.key.llm.FileAccess;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.ShellSafetyPolicy;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The {@code shell} tool: executes a shell command inside the model jail. Requires user
 * approval (ASK) and is blocked by the {@link ShellSafetyPolicy} blocklist. The parameter
 * shape follows OpenCode ({@code command}, {@code workdir}, {@code timeout} in milliseconds);
 * long-running calls can be moved into the background while they run.
 *
 * @author Alexander Weigl
 */
public final class ShellTools implements AgentToolProvider {

    /** The default timeout of a shell call in milliseconds (OpenCode's default). */
    static final int DEFAULT_TIMEOUT_MS = 120000;

    private final ShellSafetyPolicy safetyPolicy = new ShellSafetyPolicy();

    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_SHELL, ToolCategory.SHELL,
            "Runs a shell command inside the model directory. Requires user approval."
                + " Destructive commands are blocked by a blocklist. Long-running commands"
                + " (builds, tests) can be put into the background while they run, so you can"
                + " keep asking questions.",
            Tool.ApprovalRequirement.ASK,
            AgentTool.schema("command",
                JsonSchema.builder().withType("string")
                        .withDescription("the shell command to run").build(),
                "workdir",
                JsonSchema.builder().withType("string")
                        .withDescription("working directory for the command, relative to the"
                            + " model root (default: the model root)")
                        .build(),
                "timeout",
                JsonSchema.builder().withType("integer")
                        .withDescription("timeout in milliseconds (default "
                            + DEFAULT_TIMEOUT_MS + ", capped by the configured shell timeout)")
                        .build()),
            true,
            args -> runCommand(AgentTool.stringArg(args, "command"),
                AgentTool.stringArg(args, "workdir"), AgentTool.intArg(args, "timeout"))));
    }

    private String runCommand(String command, String workdir, Integer timeoutMs) throws Exception {
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
        var proof = ProofSelector.selectedProof();
        var workDir = proof == null ? null : FileAccess.modelRoot(proof);
        if (workdir != null && !workdir.isBlank()) {
            var resolved = FileAccess.resolveInModel(proof, workdir);
            if (resolved == null || !Files.isDirectory(resolved)) {
                return "Error: not a directory inside the model directory: " + workdir;
            }
            workDir = resolved;
        }
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
        int requested = timeoutMs == null ? DEFAULT_TIMEOUT_MS : Math.max(1, timeoutMs);
        int settingsMs = Math.max(1, settings.getShellTimeoutSeconds()) * 1000;
        int timeout = Math.min(requested, settingsMs);
        int maxChars = Math.max(1, settings.getShellMaxOutputChars());

        var outFuture = CompletableFuture.supplyAsync(
            () -> readBounded(process.getInputStream(), maxChars));
        boolean done;
        try {
            done = process.waitFor(timeout, TimeUnit.MILLISECONDS);
        } catch (InterruptedException e) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
            return "Error: command interrupted";
        }
        if (!done) {
            process.destroyForcibly();
            return "[Command timed out after " + timeout + " ms and was killed]";
        }
        String out;
        try {
            out = outFuture.get(5, TimeUnit.SECONDS);
        } catch (Exception e) {
            out = "(output could not be collected)";
        }
        int exit = process.exitValue();
        var header = "[exit code: " + exit + (workDir != null ? ", workdir: " + workDir : "")
            + ", timeout: " + timeout + " ms]";
        var body = out == null || out.isBlank() ? "(no output)" : out.stripTrailing();
        return header + "\n" + body;
    }

    /** Reads at most {@code maxChars} characters from the stream (blocking). */
    private static String readBounded(java.io.InputStream stream, int maxChars) {
        try {
            var bytes = stream.readAllBytes();
            var text = new String(bytes, StandardCharsets.UTF_8);
            if (text.length() > maxChars) {
                text = text.substring(0, maxChars) + "\n... [output truncated at " + maxChars
                    + " characters]";
            }
            return text;
        } catch (IOException e) {
            return "(output could not be read: " + e.getMessage() + ")";
        }
    }
}
