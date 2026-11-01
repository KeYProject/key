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
import java.util.HashSet;
import java.util.List;

import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.Nullable;

/**
 * Shared plumbing for the file-backed user libraries (prompts and skills). Content is stored as
 * Markdown files with a YAML front matter ({@link MarkdownFrontMatter}) named
 * {@code <name>.md}. The library is looked up along a configurable <em>search path</em>: the
 * ordered list of directories returned by {@link #configuredSearchPath()} (entries may use
 * {@code ~}, {@code $(pwd)} and relative paths, see {@link #expandPath(String)}); when it is
 * empty, the default directory {@code <key-config-dir>/llm/<subDirectory()>} is used, into which
 * subclasses may install shipped content on first access ({@link #ensureSeeded()}).
 * <p>
 * The search order defines the priority: if the same name exists in several directories, the
 * first occurrence wins. New entries are created in the first directory of the search path,
 * while {@link #delete(String)} removes a name from all directories. Legacy
 * {@code <name>.json} files from older KeY versions are migrated to Markdown automatically on
 * first access. Names are validated so they cannot escape the library directories.
 *
 * @author Alexander Weigl
 */
abstract class FileBackedLibrary<E> {

    private static final String MD_SUFFIX = ".md";
    private static final String JSON_SUFFIX = ".json";

    /** The directory holding the Markdown files of this library. */
    protected abstract String subDirectory();

    /** Reads a single element from its Markdown text (front matter + body). */
    protected abstract @Nullable E fromMarkdown(String markdown);

    /** Serializes a single element to Markdown text (front matter + body). */
    protected abstract String toMarkdown(E element);

    /**
     * Reads a single element from the legacy JSON format (used to migrate old files). Returns
     * {@code null} when the format is not supported / the text is invalid.
     */
    protected @Nullable E fromLegacyJson(String json) {
        return null;
    }

    /** Returns the id of an element (also the file name). */
    protected abstract String nameOf(E element);

    /** Validates a new/replacement name. Returns {@code null} when valid. */
    protected abstract String validate(E element);

    /**
     * The user-configured search path, in raw (unexpanded) form. An empty list selects the
     * default directory ({@link #defaultDir()}).
     */
    protected abstract List<String> configuredSearchPath();

    private static final java.util.regex.Pattern NAME =
        java.util.regex.Pattern.compile("[a-zA-Z0-9_-]+");

    /** The default (legacy) library directory, used when the search path is empty. */
    protected Path defaultDir() {
        if (PathConfig.currentPaths != null) {
            return PathConfig.currentPaths.keyConfigDir.resolve("llm").resolve(subDirectory());
        }
        return Path.of(System.getProperty("user.home", "."), ".key", "llm")
                .resolve(subDirectory());
    }

    /**
     * Whether {@link #ensureSeeded()} has already run (libraries are singletons, so once per JVM).
     */
    private boolean seeded;

    /**
     * One-time seeding of the library: when the search path is empty (only the default directory
     * is searched), {@link #seedDefaultDirectory(Path)} may install shipped content into it.
     * Called before the first access to the library's contents; failures are ignored (seeding is
     * best-effort).
     */
    protected void ensureSeeded() {
        if (seeded) {
            return;
        }
        seeded = true;
        if (!configuredSearchPath().isEmpty()) {
            return; // the user manages their own directories
        }
        try {
            seedDefaultDirectory(defaultDir());
        } catch (IOException | RuntimeException e) {
            // seeding must never break the library access
        }
    }

    /**
     * Seeds the given directory with shipped content; the default implementation does nothing.
     * Only called when the search path is empty, i.e. {@code dir} is the effective default
     * directory.
     */
    protected void seedDefaultDirectory(Path dir) throws IOException {
    }

    /**
     * Expands a search path entry: {@code $(pwd)} is replaced by the working directory, a
     * leading {@code ~} by the home directory, and relative paths are resolved against the
     * working directory.
     */
    static Path expandPath(String raw) {
        String home = System.getProperty("user.home", ".");
        String pwd = System.getProperty("user.dir", ".");
        var text = raw.strip().replace("$(pwd)", pwd);
        if (text.equals("~")) {
            text = home;
        } else if (text.startsWith("~/")) {
            text = home + text.substring(1);
        }
        var path = Path.of(text);
        return path.isAbsolute() ? path : Path.of(pwd).resolve(path);
    }

    /** The expanded search path; the default directory when no (valid) entry is configured. */
    List<Path> searchDirs() {
        var result = new ArrayList<Path>();
        for (var entry : configuredSearchPath()) {
            if (entry != null && !entry.isBlank()) {
                result.add(expandPath(entry));
            }
        }
        return result.isEmpty() ? List.of(defaultDir()) : List.copyOf(result);
    }

    public synchronized List<E> all() {
        ensureSeeded();
        var seen = new HashSet<String>();
        var result = new ArrayList<E>();
        for (var dir : searchDirs()) {
            migrateLegacy(dir);
            try {
                if (!Files.isDirectory(dir)) {
                    continue;
                }
                try (var stream = Files.list(dir)) {
                    stream.filter(p -> p.toString().endsWith(MD_SUFFIX))
                            .sorted(Comparator.comparing(Path::toString)).forEach(p -> {
                                try {
                                    var markdown = Files.readString(p, StandardCharsets.UTF_8);
                                    var e = fromMarkdown(markdown);
                                    // the first directory in the search order wins
                                    if (e != null && seen.add(nameOf(e))) {
                                        result.add(e);
                                    }
                                } catch (IOException ex) {
                                    // skip unreadable file
                                }
                            });
                }
            } catch (IOException e) {
                // skip unreadable directory
            }
        }
        result.sort(Comparator.comparing(this::nameOf));
        return result;
    }

    /**
     * Converts leftover legacy {@code <name>.json} files to the Markdown format and deletes them.
     * Existing Markdown files win: a legacy file for a name that already has a {@code .md} file
     * is deleted without conversion.
     */
    private void migrateLegacy(Path dir) {
        try {
            if (!Files.isDirectory(dir)) {
                return;
            }
            try (var stream = Files.list(dir)) {
                stream.filter(p -> p.toString().endsWith(JSON_SUFFIX)).forEach(p -> {
                    try {
                        var json = Files.readString(p, StandardCharsets.UTF_8);
                        var e = fromLegacyJson(json);
                        if (e != null) {
                            var target = dir.resolve(nameOf(e) + MD_SUFFIX);
                            if (!Files.exists(target)) {
                                Files.writeString(target, toMarkdown(e), StandardCharsets.UTF_8);
                            }
                        }
                        Files.deleteIfExists(p);
                    } catch (IOException ex) {
                        // keep the file; it will be retried on the next access
                    }
                });
            }
        } catch (IOException e) {
            // treat as empty library
        }
    }

    public synchronized E get(String name) {
        for (E e : all()) {
            if (nameOf(e).equals(name)) {
                return e;
            }
        }
        return null;
    }

    public synchronized boolean exists(String name) {
        return get(name) != null;
    }

    /**
     * Returns the file backing the entry with the given name: the first {@code <name>.md} found
     * along the search path, or {@code null} when the entry does not exist as a file.
     */
    public synchronized @Nullable Path fileOf(String name) {
        for (var dir : searchDirs()) {
            var file = dir.resolve(name + MD_SUFFIX);
            if (Files.exists(file)) {
                return file;
            }
        }
        return null;
    }

    /**
     * Saves (creates or replaces) an element in the <em>first</em> directory of the search path.
     * Files with the same name in lower-priority directories are left untouched (they are merely
     * shadowed and can be removed with {@link #delete(String)}). Returns {@code null} on success
     * or an error text.
     */
    public synchronized String save(E element) {
        var error = validate(element);
        if (error != null) {
            return error;
        }
        try {
            var dir = searchDirs().get(0);
            Files.createDirectories(dir);
            var name = nameOf(element);
            Files.writeString(dir.resolve(name + MD_SUFFIX), toMarkdown(element),
                StandardCharsets.UTF_8);
            // drop a stale legacy file of the same name
            Files.deleteIfExists(dir.resolve(name + JSON_SUFFIX));
            return null;
        } catch (IOException e) {
            return "Could not write the library file: " + e.getMessage();
        }
    }

    /**
     * Deletes the entry with the given name from <em>every</em> directory of the search path
     * (Markdown and legacy JSON files). Returns {@code null} on success (at least one file was
     * removed, or nothing existed) or an error text.
     */
    public synchronized String delete(String name) {
        boolean any = false;
        String firstError = null;
        for (var dir : searchDirs()) {
            try {
                any |= Files.deleteIfExists(dir.resolve(name + MD_SUFFIX))
                        | Files.deleteIfExists(dir.resolve(name + JSON_SUFFIX));
            } catch (IOException e) {
                if (firstError == null) {
                    firstError = "Could not delete " + name + " in " + dir + ": " + e.getMessage();
                }
            }
        }
        if (any) {
            return null;
        }
        return firstError != null ? firstError : "No such entry: " + name;
    }

    public synchronized void reload() {
        // directories are scanned on every access; nothing to cache
    }

    protected static boolean validName(String name) {
        return name != null && !name.isBlank() && NAME.matcher(name).matches();
    }
}
