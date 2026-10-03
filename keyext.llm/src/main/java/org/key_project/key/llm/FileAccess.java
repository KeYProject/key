/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.Nullable;

/**
 * Bounded and sandboxed access to the files of the current Java model. Used by the built-in file
 * tools, by the {@code @file:...} prompt references and by the file listing UI.
 * <p>
 * All operations are confined to the model directory of the current proof (the {@code jail}).
 * Absolute paths outside the jail, {@code ..} segments and symlink escapes are rejected.
 *
 * @author Alexander Weigl
 */
public final class FileAccess {
    /** Directories skipped while enumerating the model tree. */
    private static final List<String> SKIP_DIRS = List.of(".git", ".hg", ".svn", "build",
        "target", "out", "node_modules", ".gradle", ".idea", ".classpath");

    /** Extensions treated as binary and listed but not offered for reading. */
    private static final List<String> BINARY_EXTENSIONS =
        List.of(".class", ".jar", ".jpg", ".jpeg", ".png", ".gif", ".webp", ".pdf", ".zip",
            ".gz", ".bin", ".o", ".so", ".dll");

    private FileAccess() {
    }

    /** Returns the model directory of the given proof, or {@code null} if unavailable. */
    public static @Nullable Path modelRoot(@Nullable Proof proof) {
        if (proof == null) {
            return null;
        }
        var javaModel = proof.getEnv().getServicesForEnvironment().getJavaModel();
        return javaModel == null ? null : javaModel.getModelDir();
    }

    /**
     * Lists regular files under the model directory, bounded to
     * {@link LlmSettings#getMaxModelListingEntries()} entries. Never returns {@code null}.
     */
    public static List<Path> listFiles(@Nullable Proof proof) {
        return listFiles(proof, LlmSettings.INSTANCE.getMaxModelListingEntries());
    }

    /** Lists regular files, bounded to {@code limit} entries. */
    public static List<Path> listFiles(@Nullable Proof proof, int limit) {
        var root = modelRoot(proof);
        if (root == null) {
            return List.of();
        }
        if (!Files.exists(root)) {
            return List.of();
        }
        try {
            if (Files.isRegularFile(root)) {
                return List.of(root);
            }
            var result = new ArrayList<Path>();
            try (var stream = Files.walk(root)) {
                stream.limit(2L * limit).forEach(p -> {
                    if (result.size() < limit && Files.isRegularFile(p)) {
                        result.add(p);
                    }
                });
            }
            result.sort(Comparator.comparing(p -> relative(root, p)));
            return result;
        } catch (IOException e) {
            return List.of();
        }
    }

    private static String relative(Path root, Path p) {
        try {
            return root.relativize(p).toString();
        } catch (IllegalArgumentException e) {
            return p.toString();
        }
    }

    /**
     * Resolves a possibly relative path against the model jail. Returns {@code null} if the
     * resolved path escapes the jail (or the jail is unavailable).
     */
    public static @Nullable Path resolveInModel(@Nullable Proof proof, String requested) {
        var root = modelRoot(proof);
        if (root == null) {
            return null;
        }
        Path resolved;
        var req = Path.of(requested);
        if (req.isAbsolute()) {
            resolved = req.normalize();
        } else {
            resolved = root.resolve(req).normalize();
        }
        if (!resolved.startsWith(root)) {
            return null;
        }
        return resolved;
    }

    /** Reads a text file, bounded to the settings' size and character caps. */
    public static String readText(Path path) throws IOException {
        if (!Files.isRegularFile(path)) {
            throw new IOException("not a regular file: " + path);
        }
        long maxBytes = LlmSettings.INSTANCE.getMaxFileSizeKB() * 1024L;
        if (Files.size(path) > maxBytes) {
            throw new IOException("file larger than maxFileSizeKB");
        }
        var text = Files.readString(path, StandardCharsets.UTF_8);
        int cap = Math.max(1, LlmSettings.INSTANCE.getMaxFileContentChars());
        if (text.length() > cap) {
            text = text.substring(0, cap) + "\n... [truncated]";
        }
        return text;
    }

    /** Whether a file is considered binary (by extension) and not offered for reading. */
    public static boolean isBinary(String fileName) {
        var lower = fileName.toLowerCase();
        for (String ext : BINARY_EXTENSIONS) {
            if (lower.endsWith(ext)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the relative name of a file inside the model tree (or its absolute path if it is
     * outside), used for {@code @file:...} references.
     */
    public static @Nullable String relativeName(@Nullable Proof proof, Path absolute) {
        var root = modelRoot(proof);
        if (root == null) {
            return absolute.toString();
        }
        try {
            if (absolute.startsWith(root)) {
                return root.relativize(absolute).toString();
            }
        } catch (IllegalArgumentException e) {
            // fall through
        }
        return null;
    }

    /** Directories that are always skipped during enumeration. */
    public static List<String> skipDirectories() {
        return SKIP_DIRS;
    }
}
