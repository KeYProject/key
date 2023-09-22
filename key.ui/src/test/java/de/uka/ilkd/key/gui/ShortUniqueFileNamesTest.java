/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.nio.file.Paths;
import java.util.*;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * @author Julian Wiesler
 */
class ShortUniqueFileNamesTest {
    @Test
    void uniqueFileNamesTest() {
        // (path, expected name after all insertions)
        HashMap<String, String> pathsToName = new HashMap<>();
        pathsToName.put(Paths.get("z", "a", "b", "c").toString(),
            Paths.get("z", "a", "b", "c").toString());
        pathsToName.put(Paths.get("a", "b", "c").toString(), Paths.get("a", "b", "c").toString());
        pathsToName.put(Paths.get("b", "b", "c").toString(), Paths.get("b", "b", "c").toString());
        pathsToName.put(Paths.get("z", "b", "b", "c").toString(),
            Paths.get("z", "b", "b", "c").toString());
        pathsToName.put(Paths.get("b", "c").toString(), Paths.get("b", "c").toString());
        pathsToName.put(Paths.get("b", "d").toString(), Paths.get("d").toString());
        pathsToName.put(Paths.get("x", "y").toString(), Paths.get("y").toString());
        Random random = new Random(42);

        // Test that insertion order does not matter
        String[] paths = pathsToName.keySet().toArray(String[]::new);

        for (int i = 0; i < 1000; ++i) {
            Collections.shuffle(Arrays.asList(paths), random);
            ShortUniqueFileNames.Name[] names = ShortUniqueFileNames.makeUniqueNames(paths);
            Assertions.assertEquals(names.length, paths.length);

            for (int j = 0; j < paths.length; ++j) {
                String path = paths[j];
                ShortUniqueFileNames.Name name = names[j];
                Assertions.assertEquals(path, name.getPath());

                String expected = pathsToName.get(path);
                String actual = name.getName();
                Assertions.assertEquals(expected, actual, "Name for " + path);
            }
        }
    }
}
