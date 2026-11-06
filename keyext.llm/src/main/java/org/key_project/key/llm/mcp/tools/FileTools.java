/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.key_project.key.llm.FileAccess;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The file-access tools {@code list_files}, {@code read_file}, {@code edit_file} and
 * {@code file_info}: bounded, sandboxed access to the files of the current Java model directory.
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
            AgentTool.tool(KeYAgentTools.TOOL_EDIT_FILE, ToolCategory.FILES,
                "Performs an exact string replacement in a text file of the current Java model"
                    + " directory (relative path). The 'old_string' must occur exactly once in"
                    + " the file unless 'replace_all' is set; include surrounding context to make"
                    + " it unique. Read the file before editing it.",
                Tool.ApprovalRequirement.ASK,
                JsonSchema.builder().withType("object")
                        .addProperty("path",
                            JsonSchema.builder().withType("string")
                                    .withDescription("relative path inside the model").build())
                        .addProperty("old_string",
                            JsonSchema.builder().withType("string")
                                    .withDescription("the exact text to replace, including"
                                        + " enough context to be unique")
                                    .build())
                        .addProperty("new_string",
                            JsonSchema.builder().withType("string")
                                    .withDescription("the replacement text (empty string"
                                        + " deletes the text)")
                                    .build())
                        .addProperty("replace_all",
                            JsonSchema.builder().withType("boolean")
                                    .withDescription("replace every occurrence of old_string"
                                        + " (default false)")
                                    .build())
                        .withRequired(List.of("path", "old_string", "new_string"))
                        .build(),
                args -> editFile(AgentTool.stringArg(args, "path"),
                    AgentTool.stringArg(args, "old_string"),
                    AgentTool.stringArg(args, "new_string"),
                    AgentTool.boolArg(args, "replace_all"))),
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

    /**
     * The {@code edit_file} body: resolves {@code path} inside the model directory (sandbox),
     * rejects binary files, and applies the search/replace to the file.
     */
    private static String editFile(String path, String oldString, String newString,
            boolean replaceAll) {
        if (path == null || path.isBlank()) {
            return "Error: 'path' parameter is required";
        }
        if (oldString == null) {
            return "Error: 'old_string' parameter is required";
        }
        if (newString == null) {
            return "Error: 'new_string' parameter is required";
        }
        if (oldString.isEmpty()) {
            return "Error: 'old_string' must not be empty";
        }
        var proof = ProofSelector.selectedProof();
        if (proof == null) {
            return "Error: no proof selected; no model directory available";
        }
        var resolved = FileAccess.resolveInModel(proof, path);
        if (resolved == null || !Files.exists(resolved) || !Files.isRegularFile(resolved)) {
            return "Error: file not found inside the model directory: " + path;
        }
        if (FileAccess.isBinary(path)) {
            return "Error: binary file (not offered for editing): " + path;
        }
        return applyEdit(resolved, path, oldString, newString, replaceAll);
    }

    /**
     * Applies an exact search/replace to {@code file}: {@code oldString} must occur exactly once
     * (unless {@code replaceAll}); every occurrence is replaced by {@code newString} and the file
     * is written back. Returns {@code null}-free error texts on failure ("Error: ...") and a
     * summary on success. Package-private so the semantics can be tested headless.
     */
    static String applyEdit(Path file, String displayPath, String oldString, String newString,
            boolean replaceAll) {
        if (oldString == null) {
            return "Error: 'old_string' parameter is required";
        }
        if (newString == null) {
            return "Error: 'new_string' parameter is required";
        }
        if (oldString.isEmpty()) {
            return "Error: 'old_string' must not be empty";
        }
        String content;
        try {
            long maxBytes = LlmSettings.INSTANCE.getMaxFileSizeKB() * 1024L;
            if (Files.size(file) > maxBytes) {
                return "Error: file larger than maxFileSizeKB (" + maxBytes / 1024 + " KiB): "
                    + displayPath;
            }
            content = Files.readString(file, StandardCharsets.UTF_8);
        } catch (IOException e) {
            return "Error: could not read the file: " + e.getMessage();
        }
        if (oldString.isEmpty()) {
            return "Error: 'old_string' must not be empty";
        }
        int occurrences = countOccurrences(content, oldString);
        if (occurrences == 0) {
            return "Error: old_string not found in " + displayPath
                + " (read the file again; the content may have changed)";
        }
        if (occurrences > 1 && !replaceAll) {
            return "Error: old_string occurs " + occurrences + " times in " + displayPath
                + "; include more surrounding context to make it unique, or pass"
                + " replace_all=true to replace every occurrence";
        }
        var updated = replaceAll ? content.replace(oldString, newString)
                : content.replaceFirst(Pattern.quote(oldString),
                    Matcher.quoteReplacement(newString));
        try {
            Files.writeString(file, updated, StandardCharsets.UTF_8);
        } catch (IOException e) {
            return "Error: could not write the file: " + e.getMessage();
        }
        return "Replaced " + (replaceAll ? occurrences : 1) + " occurrence(s) in " + displayPath
            + " (new size: " + updated.length() + " chars).";
    }

    /** The number of non-overlapping occurrences of {@code needle} in {@code haystack}. */
    private static int countOccurrences(String haystack, String needle) {
        if (needle.isEmpty()) {
            return 0; // an empty needle would match at every position (and never advance)
        }
        int count = 0;
        for (int index = haystack.indexOf(needle); index >= 0; index =
            haystack.indexOf(needle, index + needle.length())) {
            count++;
        }
        return count;
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
