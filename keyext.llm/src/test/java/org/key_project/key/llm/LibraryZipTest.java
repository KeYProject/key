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
import java.util.zip.ZipOutputStream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests the ZIP-based export/import of the user libraries: an export holds one
 * {@code <name>.md} entry per element and reading it back yields exactly the written entries,
 * directories are skipped.
 */
class LibraryZipTest {

    @TempDir
    Path tempDir;

    @Test
    void zipRoundTrip() throws IOException {
        var target = tempDir.resolve("lib.zip");
        var entries = new LinkedHashMap<String, String>();
        entries.put("optics.md", "---\nname: optics\n---\nInstructions body.");
        entries.put("prove.md", "---\nname: prove\n---\nProve $seq.");
        entries.put("nested/sub.md", "---\nname: sub\n---\nbody");

        LibraryZip.write(target, entries);

        Map<String, String> back = LibraryZip.read(target);
        assertEquals(entries, back);
    }

    @Test
    void readSkipsDirectoriesAndKeepsUtf8() throws IOException {
        var target = tempDir.resolve("dirs.zip");
        var utf8 = "äöü — ünïcödé \uD83D\uDE00 \u00FC";
        try (var out = new ZipOutputStream(Files.newOutputStream(target))) {
            out.putNextEntry(new ZipEntry("sub/"));
            out.closeEntry();
            out.putNextEntry(new ZipEntry("sub/a.md"));
            out.write(utf8.getBytes(StandardCharsets.UTF_8));
            out.closeEntry();
        }

        Map<String, String> back = LibraryZip.read(target);
        assertEquals(Map.of("sub/a.md", utf8), back);
    }
}
