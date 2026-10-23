/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
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

/**
 * The {@code run_command} tool: executes a shell command in the model directory. Requires user
 * approval (ASK) and is blocked by the {@link ShellSafetyPolicy} blocklist.
 *
 * @author Alexander Weigl
 */
public final class ShellTools implements AgentToolProvider {
    private final ShellSafetyPolicy safetyPolicy = new ShellSafetyPolicy();

    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_RUN_COMMAND,
            "Runs a shell command in the model directory. Requires user approval. Destructive"
                + " commands are blocked by a blocklist.",
            Tool.ApprovalRequirement.ASK,
            AgentTool.schema("command",
                JsonSchema.builder().withType("string")
                        .withDescription("the shell command to run").build()),
            args -> runCommand(AgentTool.stringArg(args, "command"))));
    }

    private String runCommand(String command) throws Exception {
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
}
