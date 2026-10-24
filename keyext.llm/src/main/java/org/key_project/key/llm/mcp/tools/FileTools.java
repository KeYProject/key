/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.file.Files;
import java.util.List;
import java.util.stream.Collectors;

import org.key_project.key.llm.FileAccess;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The file-access tools {@code list_files}, {@code read_file} and {@code file_info}: bounded,
 * sandboxed access to the files of the current Java model directory.
 *
 * @author Alexander Weigl
 */
public final class FileTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_LIST_FILES, ToolCategory.FILES,
                "Lists files of the current Java model directory (relative paths, bounded)."
                    + " Use with an optional prefix to filter.",
                AgentTool.schema("prefix",
                    JsonSchema.builder().withType("string")
                            .withDescription("optional path prefix to filter").build()),
                args -> listFiles(AgentTool.stringArg(args, "prefix"))),
            AgentTool.tool(KeYAgentTools.TOOL_READ_FILE, ToolCategory.FILES,
                "Reads a text file of the current Java model directory (relative path)."
                    + " Respects the configured size limits.",
                AgentTool.schema("path",
                    JsonSchema.builder().withType("string")
                            .withDescription("relative path inside the model")
                            .build()),
                args -> readFile(AgentTool.stringArg(args, "path"), false)),
            AgentTool.tool(KeYAgentTools.TOOL_FILE_INFO, ToolCategory.FILES,
                "Returns metadata (size, last modified, kind) of a file inside the model"
                    + " directory.",
                AgentTool.schema("path",
                    JsonSchema.builder().withType("string")
                            .withDescription("relative path inside the model")
                            .build()),
                args -> readFile(AgentTool.stringArg(args, "path"), true)));
    }

    private static String listFiles(String prefix) {
        var proof = ProofSelector.selectedProof();
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

    private static String readFile(String path, boolean info) {
        if (path == null || path.isBlank()) {
            return "Error: 'path' parameter is required";
        }
        var proof = ProofSelector.selectedProof();
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
}
