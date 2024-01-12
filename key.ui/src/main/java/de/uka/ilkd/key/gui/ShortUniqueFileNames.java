/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.io.File;

/**
 * Algorithm to construct short unique file names for a set of paths.
 *
 * Example: [src/main/java, src/test/java] => [main/java, test/java]
 *
 * @author Julian Wiesler
 */
public final class ShortUniqueFileNames {
    private ShortUniqueFileNames() {

    }

    /**
     * This is a helper function for prepareForInsertionOf and needs all invariants from there.
     *
     * @param entry An entry whose name ends with shorter's name
     * @param shorter An entry
     */
    private static void resolveDuplicate(Name entry, Name shorter) {
        // First, resolve cases like entry = a/(b/c) and shorter = b/b/(c)
        while (entry.getName().endsWith(shorter.getName())
                && entry.getName().length() != shorter.getName().length()) {
            // By extending shorter's name
            boolean shorterCanBeMadeLonger = shorter.makeNameLonger();
            // return if we resolved the duplicate
            if (!entry.getName().endsWith(shorter.getName())) {
                return;
            }

            // break if shorter can't be made longer
            if (!shorterCanBeMadeLonger) {
                break;
            }
        }

        // When we are here, we have a common stem of the same length
        // E.g. entry = a/(b/c) and shorter = b/(b/c)
        while (true) {
            // extend both
            boolean firstCanBeMadeLonger = entry.makeNameLonger();
            boolean secondCanBeMadeLonger = shorter.makeNameLonger();
            // break if we resolved the duplicate or neither one can be made longer
            if (!entry.getName().equals(shorter.getName())
                    || !(firstCanBeMadeLonger || secondCanBeMadeLonger)) {
                break;
            }
        }
    }

    /**
     * Renames all files (including entry) to give entry a unique name.
     * entry must have the default name given by the constructor (the file name of its full path).
     *
     * @param files already existing files, they must have unique names and must not contain
     *        entry
     * @param entry the entry that should be prepared for
     */
    private static void prepareForInsertionOf(
            Name[] files,
            int count,
            Name entry) {
        for (int i = 0; i < count; ++i) {
            Name e = files[i];
            if (e.getName().endsWith(entry.getName())) {
                // Resolve duplicate provides a unique name for e and entry
                // This need not be unique in all names (yet)

                // Observation 1: extending existing names does not produce duplicates in the
                // existing names

                // Observation 2: resolve duplicate might not extend `entry`'s name far enough
                // However, this is ok since the entry with the largest constraint is reached
                // eventually and `entry`'s name is extended far enough.
                // Example for this: entries = [(b/c), (a/b/c)] and entry = z/a/b/(c)
                // first iteration with (b/c) and z/a/b/(c) leads to z/(a/b/c)
                // second iteration with (a/b/c) and z/(a/b/c) leads to (z/a/b/c)

                resolveDuplicate(e, entry);
            }
        }
    }

    /**
     * Constructs short unique names for the given unique file paths
     *
     * @param files unique list of files
     * @return named files
     */
    public static Name[] makeUniqueNames(String[] files) {
        Name[] names = new Name[files.length];
        for (int i = 0; i < files.length; i++) {
            Name entry = new Name(files[i]);
            prepareForInsertionOf(names, i, entry);
            names[i] = entry;
        }

        return names;
    }

    /**
     * Wrapper for a substring of a path
     */
    public static class Name {
        /** full path */
        private final String path;
        /** substring of path used as name */
        private String name;
        /** start position of name in path */
        private int nameStart;

        /**
         * Constructor
         *
         * @param path the full path
         */
        public Name(String path) {
            this.path = path;
            this.nameStart = path.length();
            makeNameLonger();
        }

        /**
         * @return the full path
         */
        public String getPath() {
            return path;
        }

        /**
         * @return a substring of the path that is used as the name
         */
        public String getName() {
            return name;
        }

        private int getNextNameStart() {
            return path.lastIndexOf(File.separatorChar, this.nameStart - 1);
        }

        /**
         * Try to make the name longer
         *
         * @return true if the name was made longer
         */
        public boolean makeNameLonger() {
            if (this.nameStart == -1) {
                return false;
            }
            this.nameStart = getNextNameStart();
            this.name = path.substring(nameStart + 1);
            return true;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return path.substring(0, nameStart + 1) + "(" + name + ")";
        }
    }
}
