package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.util.Pair;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Random;

/**
 * @author Julian Wiesler
 */
class RecentFilesTest {
    @Test
    void prefixRecentUniqueFileNames() {
        // (path, expected name after all insertions)
        var paths = Arrays.asList(
            new Pair<>(Paths.get("z", "a", "b", "c").toString(),
                Paths.get("z", "a", "b", "c").toString()),
            new Pair<>(Paths.get("a", "b", "c").toString(), Paths.get("a", "b", "c").toString()),
            new Pair<>(Paths.get("b", "b", "c").toString(), Paths.get("b", "b", "c").toString()),
            new Pair<>(Paths.get("z", "b", "b", "c").toString(),
                Paths.get("z", "b", "b", "c").toString()),
            new Pair<>(Paths.get("b", "c").toString(), Paths.get("b", "c").toString()),
            new Pair<>(Paths.get("b", "d").toString(), Paths.get("d").toString()),
            new Pair<>(Paths.get("x", "y").toString(), Paths.get("y").toString()));
        Random random = new Random(42);

        // Test that insertion order does not matter
        for (int i = 0; i < 1000; ++i) {
            Collections.shuffle(paths, random);
            var entries = new HashMap<String, RecentFileMenu.RecentFileEntry>();
            for (Pair<String, String> pair : paths) {
                var e = new RecentFileMenu.RecentFileEntry(pair.first);
                RecentFileMenu.prepareForInsertionOf(entries.values(), e);
                entries.put(e.getAbsolutePath(), e);
            }

            for (Pair<String, String> pair : paths) {
                String expected = pair.second;
                String actual = entries.get(pair.first).getName();
                Assertions.assertEquals(expected, actual, "Name for " + pair.first);
            }
        }
    }
}
