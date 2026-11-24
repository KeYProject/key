/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.nio.file.Files;
import java.nio.file.Path;

import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;


/**
 * Regression test for issue #3711: after loading the recent-files list from disk, the "most
 * recent" file (used by the Reload action) must be the first entry of the stored list. Previously
 * {@code RecentFileMenu.loadFrom} left {@code mostRecentFile} null after startup because of an
 * inverted condition, so Reload picked the wrong (or no) file.
 */
class RecentFileMenuTest {

    @Test
    void mostRecentFilesTempFilesAreNotReloadedIfNotExisting(@TempDir Path tmp) throws Exception {
        Path fileA = tmp.resolve("C.key");
        Path fileB = tmp.resolve("D.key");

        // do not create these files.

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFileNoSave(fileA.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFileNoSave(fileB.toAbsolutePath().toString(), null, false, null);

        Path store = tmp.resolve("recent.json");
        menu.store(store);

        // mainWindow is only stored as a field and not used on the loadFrom/getMostRecent path.
        RecentFileMenu menu2 = new RecentFileMenu(null);
        menu2.loadFrom(store);

        Assertions.assertThat(menu2.getMostRecent()).isEqualTo(menu.getMostRecent());
        Assertions.assertThat(menu2.getEntries()).isEmpty(); // <- non existing temp files
    }

    @Test
    void mostRecentFilesTempFilesAreNotReloadedIfExisting(@TempDir Path tmp) throws Exception {
        Path fileA = tmp.resolve("A.key");
        Path fileB = tmp.resolve("B.key");

        Files.createFile(fileA);
        Files.createFile(fileB);

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFileNoSave(fileA.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFileNoSave(fileB.toAbsolutePath().toString(), null, false, null);

        Path store = tmp.resolve("recent.json");
        menu.store(store);

        // mainWindow is only stored as a field and not used on the loadFrom/getMostRecent path.
        RecentFileMenu menu2 = new RecentFileMenu(null);
        menu2.loadFrom(store);

        Assertions.assertThat(menu2.getMostRecent()).isEqualTo(menu.getMostRecent());
        Assertions.assertThat(menu2.getEntries()).containsExactlyElementsOf(menu.getEntries());
    }

    @Test
    void recentFoldersAreUniqueAndMostRecentFirst(@TempDir Path tmp) throws Exception {
        Path folderA = Files.createDirectory(tmp.resolve("a"));
        Path folderB = Files.createDirectory(tmp.resolve("b"));
        Path fileA1 = Files.createFile(folderA.resolve("A1.key"));
        Path fileB = Files.createFile(folderB.resolve("B.key"));
        Path fileA2 = Files.createFile(folderA.resolve("A2.key"));

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFileNoSave(fileA1.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFileNoSave(fileB.toAbsolutePath().toString(), null, false, null);
        menu.addRecentFileNoSave(fileA2.toAbsolutePath().toString(), null, false, null);

        Assertions.assertThat(menu.getRecentFolders())
                .containsExactly(folderA.toFile().getAbsoluteFile(),
                    folderB.toFile().getAbsoluteFile());
    }

    @Test
    void recentFoldersSkipDirectoriesThatNoLongerExist(@TempDir Path tmp) throws Exception {
        Path folder = Files.createDirectory(tmp.resolve("gone"));
        Path file = Files.createFile(folder.resolve("G.key"));

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFileNoSave(file.toAbsolutePath().toString(), null, false, null);
        Files.delete(file);
        Files.delete(folder);

        Assertions.assertThat(menu.getRecentFolders()).isEmpty();
    }

    @Test
    void recentDirectoryIsReturnedAsItself(@TempDir Path tmp) throws Exception {
        Path folder = Files.createDirectory(tmp.resolve("project"));

        RecentFileMenu menu = new RecentFileMenu(null);
        menu.addRecentFileNoSave(folder.toAbsolutePath().toString(), null, false, null);

        Assertions.assertThat(menu.getRecentFolders())
                .containsExactly(folder.toFile().getAbsoluteFile());
    }
}
