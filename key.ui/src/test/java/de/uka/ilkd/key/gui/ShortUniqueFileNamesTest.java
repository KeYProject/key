/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.Random;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * @author Julian Wiesler
 */
class ShortUniqueFileNamesTest {
    @Test
    void uniqueFileNamesTest() {
        // (path, expected name after all insertions)
        var pathsToName = Map.of(
            createPathString("z", "a", "b", "c"),
            createPathString("z", "a", "b", "c"),

            createPathString("a", "b", "c"),
            createPathString("a", "b", "c"),

            createPathString("b", "b", "c"),
            createPathString("b", "b", "c"),

            createPathString("z", "b", "b", "c"),
            createPathString("z", "b", "b", "c"),

            createPathString("b", "c"),
            createPathString("b", "c"),

            createPathString("b", "d"), createPathString("d"),
            createPathString("x", "y"), createPathString("y"));

        Random random = new Random(42);

        // Test that insertion order does not matter
        var paths = new ArrayList<>(pathsToName.keySet()); // weigl: enforce array list for
                                                           // efficient shuffle.

        for (int i = 0; i < 1000; ++i) {
            Collections.shuffle(paths, random);
            ShortUniqueFileNames.Name[] names = ShortUniqueFileNames.makeUniqueNames(paths);
            Assertions.assertEquals(names.length, paths.size());

            for (int j = 0; j < paths.size(); ++j) {
                String path = paths.get(j);
                ShortUniqueFileNames.Name name = names[j];
                Assertions.assertEquals(path, name.getPath());

                String expected = pathsToName.get(path);
                String actual = name.getName();
                Assertions.assertEquals(expected, actual, "Name for " + path);
            }
        }
    }

    private static @NonNull String createPathString(String s, String... more) {
        return Paths.get(s, more).toString();
    }
}
