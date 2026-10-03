/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import de.uka.ilkd.key.settings.PathConfig;

/**
 * Shared plumbing for the file-backed user libraries (prompts and skills). Content is stored as
 * human-readable JSON files under {@code <key-config-dir>/llm/prompts|skills/<name>.json}. Names
 * are validated so they cannot escape the library directory.
 *
 * @author Alexander Weigl
 */
abstract class FileBackedLibrary<E> {

    /** The directory holding the JSON files of this library. */
    protected abstract String subDirectory();

    /** Reads a single element from its JSON text. */
    protected abstract E fromJson(String json);

    /** Serializes a single element to JSON text. */
    protected abstract String toJson(E element);

    /** Returns the id of an element (also the file name). */
    protected abstract String nameOf(E element);

    /** Validates a new/replacement name. Returns {@code null} when valid. */
    protected abstract String validate(E element);

    private static final java.util.regex.Pattern NAME =
        java.util.regex.Pattern.compile("[a-zA-Z0-9_-]+");

    protected Path baseDir() {
        if (PathConfig.currentPaths != null) {
            return PathConfig.currentPaths.keyConfigDir.resolve("llm").resolve(subDirectory());
        }
        return Path.of(System.getProperty("user.home", "."), ".key", "llm")
                .resolve(subDirectory());
    }

    public synchronized List<E> all() {
        var dir = baseDir();
        var result = new ArrayList<E>();
        try {
            if (!Files.isDirectory(dir)) {
                return result;
            }
            try (var stream = Files.list(dir)) {
                stream.filter(p -> p.toString().endsWith(".json"))
                        .sorted(Comparator.comparing(Path::toString)).forEach(p -> {
                            try {
                                var json = Files.readString(p, StandardCharsets.UTF_8);
                                var e = fromJson(json);
                                if (e != null) {
                                    result.add(e);
                                }
                            } catch (IOException ex) {
                                // skip unreadable file
                            }
                        });
            }
        } catch (IOException e) {
            // treat as empty library
        }
        return result;
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

    /** Saves (creates or replaces) an element. Returns {@code null} on success or an error text. */
    public synchronized String save(E element) {
        var error = validate(element);
        if (error != null) {
            return error;
        }
        try {
            Files.createDirectories(baseDir());
            var target = baseDir().resolve(nameOf(element) + ".json");
            Files.writeString(target, toJson(element), StandardCharsets.UTF_8);
            return null;
        } catch (IOException e) {
            return "Could not write library file: " + e.getMessage();
        }
    }

    public synchronized String delete(String name) {
        var file = baseDir().resolve(name + ".json");
        try {
            if (Files.deleteIfExists(file)) {
                return null;
            }
            return "No such entry: " + name;
        } catch (IOException e) {
            return "Could not delete " + name + ": " + e.getMessage();
        }
    }

    public synchronized void reload() {
        // directories are scanned on every access; nothing to cache
    }

    protected static boolean validName(String name) {
        return name != null && !name.isBlank() && NAME.matcher(name).matches();
    }
}
