/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * ZIP-based export/import for the file-backed user libraries (skills and prompts): an export is a
 * ZIP archive holding one {@code <name>.md} entry per library element (the Markdown document as
 * written by {@link MarkdownFrontMatter}), so the archive can be unzipped next to the existing
 * library files and extended entries are interchangeable with files on disk.
 *
 * @author Alexander Weigl
 */
public final class LibraryZip {

    private LibraryZip() {
    }

    /** Writes the given entries (archive path -&gt; UTF-8 content) as a ZIP archive. */
    public static void write(Path target, Map<String, String> entries) throws IOException {
        try (var out = new ZipOutputStream(Files.newOutputStream(target))) {
            for (var entry : entries.entrySet()) {
                out.putNextEntry(new ZipEntry(entry.getKey()));
                out.write(entry.getValue().getBytes(StandardCharsets.UTF_8));
                out.closeEntry();
            }
        }
    }

    /** Reads a ZIP archive into a map of archive path -&gt; UTF-8 content (directories skipped). */
    public static Map<String, String> read(Path source) throws IOException {
        var result = new LinkedHashMap<String, String>();
        try (var in = new ZipInputStream(Files.newInputStream(source))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                if (!entry.isDirectory()) {
                    result.put(entry.getName(),
                        new String(in.readAllBytes(), StandardCharsets.UTF_8));
                }
                in.closeEntry();
            }
        }
        return result;
    }
}
