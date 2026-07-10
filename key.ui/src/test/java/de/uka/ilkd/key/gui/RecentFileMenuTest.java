/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.nio.file.Files;
import java.nio.file.Path;

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
    void mostRecentFilesTempFilesAreNotReloadedIfNotExisting(@TempDir Path tmp) throws Exception {
        Path fileA = tmp.resolve("A.key");
        Path fileB = tmp.resolve("B.key");

        // do not create these files.

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFile(fileA.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFile(fileB.toAbsolutePath().toString(), null, false, null);

        assertEquals(2, menu.getEntries().size(), "There should be two entries. Filtering happens later");

        Path store = tmp.resolve("recent.json");
        menu.store(store);

        // mainWindow is only stored as a field and not used on the loadFrom/getMostRecent path.
        RecentFileMenu menu2 = new RecentFileMenu(null);
        menu.loadFrom(store);

        assertEquals(menu.getMostRecent(), menu2.getMostRecent());
        assertEquals(menu.getEntries(), menu2.getEntries());
    }

    @Test
    void mostRecentFilesTempFilesAreNotReloadedIfExisting(@TempDir Path tmp) throws Exception {
        Path fileA = tmp.resolve("A.key");
        Path fileB = tmp.resolve("B.key");

        Files.createFile(fileA);
        Files.createFile(fileB);

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFile(fileA.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFile(fileB.toAbsolutePath().toString(), null, false, null);

        Path store = tmp.resolve("recent.json");
        menu.store(store);

        // mainWindow is only stored as a field and not used on the loadFrom/getMostRecent path.
        RecentFileMenu menu2 = new RecentFileMenu(null);
        menu.loadFrom(store);

        assertEquals(menu.getMostRecent(), menu2.getMostRecent());
        assertEquals(menu.getEntries(), menu2.getEntries());
    }
}
