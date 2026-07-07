/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.io.BufferedWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.settings.Configuration;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Regression test for issue #3711: after loading the recent-files list from disk, the "most
 * recent" file (used by the Reload action) must be the first entry of the stored list. Previously
 * {@code RecentFileMenu.loadFrom} left {@code mostRecentFile} null after startup because of an
 * inverted condition, so Reload picked the wrong (or no) file.
 */
class RecentFileMenuTest {

    @Test
    void mostRecentIsFirstEntryAfterLoad(@TempDir Path tmp) throws Exception {
        Path fileA = tmp.resolve("A.key");
        Path fileB = tmp.resolve("B.key");

        Path store = tmp.resolve("recent.props");
        writeRecentFileStore(store, fileA, fileB);

        // mainWindow is only stored as a field and not used on the loadFrom/getMostRecent path.
        RecentFileMenu menu = new RecentFileMenu(null);
        menu.loadFrom(store);

        assertEquals(fileA.toString(), menu.getMostRecent(),
            "Reload should target the first (most recent) stored entry");
    }

    /** Writes a recent-files configuration in the same format {@code RecentFileMenu.store} uses. */
    private static void writeRecentFileStore(Path store, Path... paths) throws Exception {
        List<Configuration> entries = java.util.Arrays.stream(paths).map(p -> {
            Configuration c = new Configuration();
            c.set("path", p.toString());
            c.set("singleJava", false);
            return c;
        }).toList();
        try (BufferedWriter w = Files.newBufferedWriter(store)) {
            new Configuration.ConfigurationWriter(w).printValue(entries);
        }
    }
}
