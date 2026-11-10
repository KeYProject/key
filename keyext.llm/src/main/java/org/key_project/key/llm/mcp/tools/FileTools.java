/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.ArrayList;
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
 * The file tools {@code glob}, {@code read} and {@code edit}: bounded, sandboxed access to the
 * files of the current Java model directory, following OpenCode's tool shapes (camelCase
 * parameters and defaults).
 *
 * @author Alexander Weigl
 */
public final class FileTools implements AgentToolProvider {

    /** The default and maximum number of lines returned by {@code read}. */
    static final int READ_LINE_LIMIT = 2000;

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_GLOB, ToolCategory.FILES,
                "Matches files of the current Java model directory against a glob pattern"
                    + " (relative paths, bounded, sorted). The pattern is matched against the"
                    + " path relative to the model root; use \"**\" for any depth (default).",
                AgentTool.schema("pattern",
                    JsonSchema.builder().withType("string")
                            .withDescription("glob pattern against the relative path,"
                                + " e.g. \"**/*.java\" (default \"**\")")
                            .build(),
                    "path",
                    JsonSchema.builder().withType("string")
                            .withDescription("optional subdirectory to search in (relative to"
                                + " the model root)")
                            .build(),
                    "hidden",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("include hidden files and directories (dot"
                                + " segments); default false")
                            .build(),
                    "limit",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of matches (default 100)")
                            .build()),
                args -> globFiles(AgentTool.stringArg(args, "pattern"),
                    AgentTool.stringArg(args, "path"), AgentTool.boolArg(args, "hidden"),
                    AgentTool.intArg(args, "limit"))),
            AgentTool.tool(KeYAgentTools.TOOL_READ, ToolCategory.FILES,
                "Reads a text file of the current Java model directory (relative path) and"
                    + " returns it with line numbers. Bounds: the configured file size and"
                    + " character caps, plus " + READ_LINE_LIMIT + " lines per call (pass"
                    + " 'offset'/'limit' for more). A directory path lists its entries instead.",
                AgentTool.schema("path",
                    JsonSchema.builder().withType("string")
                            .withDescription("relative path inside the model").build(),
                    "offset",
                    JsonSchema.builder().withType("integer")
                            .withDescription("1-based line number to start reading from"
                                + " (default 1)")
                            .build(),
                    "limit",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of lines to return (default "
                                + READ_LINE_LIMIT + ")")
                            .build()),
                args -> readFile(AgentTool.stringArg(args, "path"),
                    AgentTool.intArg(args, "offset"), AgentTool.intArg(args, "limit"))),
            AgentTool.tool(KeYAgentTools.TOOL_EDIT, ToolCategory.FILES,
                "Performs an exact string replacement in a text file of the current Java model"
                    + " directory (relative path). The 'oldString' must occur exactly once in"
                    + " the file unless 'replaceAll' is set; include surrounding context to make"
                    + " it unique. Read the file before editing it.",
                Tool.ApprovalRequirement.ASK,
                JsonSchema.builder().withType("object")
                        .addProperty("path",
                            JsonSchema.builder().withType("string")
                                    .withDescription("relative path inside the model").build())
                        .addProperty("oldString",
                            JsonSchema.builder().withType("string")
                                    .withDescription("the exact text to replace, including"
                                        + " enough context to be unique")
                                    .build())
                        .addProperty("newString",
                            JsonSchema.builder().withType("string")
                                    .withDescription("the replacement text (must differ from"
                                        + " oldString; empty string deletes the text)")
                                    .build())
                        .addProperty("replaceAll",
                            JsonSchema.builder().withType("boolean")
                                    .withDescription("replace every occurrence of oldString"
                                        + " (default false)")
                                    .build())
                        .withRequired(List.of("path", "oldString", "newString"))
                        .build(),
                args -> editFile(AgentTool.stringArg(args, "path"),
                    AgentTool.stringArg(args, "oldString"),
                    AgentTool.stringArg(args, "newString"),
                    AgentTool.boolArg(args, "replaceAll"))));
    }

    // --------------------------------------------------------------------------- glob

    /**
     * The {@code glob} body: matches the files of the model tree against the glob pattern
     * (relative to the model root, forward slashes), sorted and bounded.
     */
    private static String globFiles(String pattern, String subPath, boolean hidden,
            Integer limitArg) {
        var proof = ProofSelector.selectedProof();
        var root = FileAccess.modelRoot(proof);
        if (root == null) {
            return "Error: no proof selected; no model directory available";
        }
        var base = root;
        if (subPath != null && !subPath.isBlank()) {
            var resolved = FileAccess.resolveInModel(proof, subPath);
            if (resolved == null || !Files.isDirectory(resolved)) {
                return "Error: not a directory inside the model directory: " + subPath;
            }
            base = resolved;
        }
        var glob = pattern == null || pattern.isBlank() ? "**" : pattern.trim();
        PathMatcher matcher;
        try {
            matcher = FileSystems.getDefault().getPathMatcher("glob:" + glob);
        } catch (IllegalArgumentException e) {
            return "Error: invalid glob pattern \"" + glob + "\": " + e.getMessage();
        }
        int limit = limitArg == null ? 100 : Math.max(1, Math.min(limitArg, 1000));
        long walkBound = 4L * Math.max(100, LlmSettings.INSTANCE.getMaxModelListingEntries());
        var matches = new ArrayList<String>();
        boolean truncated = false;
        try (var stream = Files.walk(base)) {
            var paths = stream.filter(Files::isRegularFile)
                    .filter(p -> visible(p, hidden) && !skipped(p))
                    .limit(walkBound)
                    .toList();
            for (var p : paths) {
                var relative = root.relativize(p).toString().replace('\\', '/');
                if (!matcher.matches(Path.of(relative))) {
                    continue;
                }
                if (matches.size() >= limit) {
                    truncated = true;
                    break;
                }
                matches.add(relative);
            }
        } catch (IOException e) {
            return "Error: could not list the model directory: " + e.getMessage();
        }
        if (matches.isEmpty()) {
            return "(no files matching glob \"" + glob + "\")";
        }
        matches.sort(String.CASE_INSENSITIVE_ORDER);
        var text = matches.stream().map(p -> "- " + p).collect(Collectors.joining("\n"));
        return truncated ? text + "\n... [truncated at limit " + limit
            + "; pass a larger 'limit' or a narrower 'pattern']" : text;
    }

    /** Whether every segment of {@code p} is visible: no dot segment unless {@code hidden}. */
    private static boolean visible(Path p, boolean hidden) {
        if (hidden) {
            return true;
        }
        for (Path part : p) {
            if (part.toString().startsWith(".")) {
                return false;
            }
        }
        return true;
    }

    /** Whether any path segment of {@code p} is a directory the file access skips. */
    private static boolean skipped(Path p) {
        for (Path part : p) {
            if (FileAccess.skipDirectories().contains(part.toString())) {
                return true;
            }
        }
        return false;
    }

    // --------------------------------------------------------------------------- read

    /**
     * The {@code read} body: a directory is listed; a text file is returned with line numbers,
     * sliced to {@code offset}/{@code limit}.
     */
    private static String readFile(String path, Integer offsetArg, Integer limitArg) {
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
        if (Files.isDirectory(resolved)) {
            return listDirectory(resolved);
        }
        if (FileAccess.isBinary(path)) {
            return "Error: binary file (not offered for reading): " + path;
        }
        String content;
        try {
            content = FileAccess.readText(resolved);
        } catch (IOException e) {
            return "Error: " + e.getMessage();
        }
        var lines = content.split("\n", -1);
        if (lines.length > 0 && lines[lines.length - 1].isEmpty()) {
            // drop the trailing empty element produced by a final newline
            lines = java.util.Arrays.copyOf(lines, lines.length - 1);
        }
        int offset = offsetArg == null ? 1 : Math.max(1, offsetArg);
        int limit = limitArg == null ? READ_LINE_LIMIT
                : Math.max(1, Math.min(limitArg, READ_LINE_LIMIT));
        if (offset > lines.length) {
            return "Error: offset " + offset + " is beyond the end of the file (" + lines.length
                + " lines)";
        }
        int end = Math.min(lines.length, offset - 1 + limit);
        var gutter = String.valueOf(lines.length).length();
        var sb = new StringBuilder();
        for (int i = offset; i <= end; i++) {
            sb.append(String.format("%" + gutter + "d\t%s%n", i, lines[i - 1]));
        }
        if (end < lines.length) {
            sb.append("... [showing lines ").append(offset).append('-').append(end).append(" of ")
                    .append(lines.length).append("; pass 'offset='").append(end + 1)
                    .append(" for the next lines]");
        }
        return sb.toString().stripTrailing();
    }

    /** Lists the entries of a directory (relative to it, directories marked with a slash). */
    private static String listDirectory(Path dir) {
        List<String> entries;
        try (var stream = Files.list(dir)) {
            entries = stream.limit(500).map(p -> {
                var name = p.getFileName().toString();
                return Files.isDirectory(p) ? name + "/" : name;
            }).sorted().toList();
        } catch (IOException e) {
            return "Error: " + e.getMessage();
        }
        return entries.isEmpty() ? "(empty directory)"
                : entries.stream().map(n -> "- " + n).collect(Collectors.joining("\n"));
    }

    // --------------------------------------------------------------------------- edit

    /**
     * The {@code edit} body: resolves {@code path} inside the model directory (sandbox),
     * rejects binary files, and applies the search/replace to the file.
     */
    private static String editFile(String path, String oldString, String newString,
            boolean replaceAll) {
        if (path == null || path.isBlank()) {
            return "Error: 'path' parameter is required";
        }
        if (oldString == null) {
            return "Error: 'oldString' parameter is required";
        }
        if (newString == null) {
            return "Error: 'newString' parameter is required";
        }
        if (oldString.isEmpty()) {
            return "Error: 'oldString' must not be empty";
        }
        if (newString.equals(oldString)) {
            return "Error: 'newString' must differ from 'oldString'";
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
            return "Error: 'oldString' parameter is required";
        }
        if (newString == null) {
            return "Error: 'newString' parameter is required";
        }
        if (oldString.isEmpty()) {
            return "Error: 'oldString' must not be empty";
        }
        if (newString.equals(oldString)) {
            return "Error: 'newString' must differ from 'oldString'";
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
        int occurrences = countOccurrences(content, oldString);
        if (occurrences == 0) {
            return "Error: oldString not found in " + displayPath
                + " (read the file again; the content may have changed)";
        }
        if (occurrences > 1 && !replaceAll) {
            return "Error: oldString occurs " + occurrences + " times in " + displayPath
                + "; include more surrounding context to make it unique, or pass"
                + " replaceAll=true to replace every occurrence";
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
}
