/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (29.03.19)
 */
public class Filenames {
    // =======================================================
    // Methods operating on Strings
    // =======================================================

    /**
     * Separates the single directory entries in a filename. The first element is an empty String
     * iff the filename is absolute. (For a Windows filename, it contains a drive letter and a
     * colon). Ignores double slashes and slashes at the end, removes references to the cwd. E.g.,
     * "/home//daniel/./key/" yields {"","home","daniel","key"}. Tries to automatically detect UNIX
     * or Windows directory delimiters. There is no check whether all other characters are valid for
     * filenames.
     */
    public static List<String> disectFilename(String filename) {

        List<String> res = new ArrayList<>();
        Path p = Paths.get(filename);
        if (p.getRoot() != null) {
            res.add(p.getRoot().toString());
        }
        for (int i = 0; i < p.getNameCount(); i++) {
            res.add(p.getName(i).toString());
        }
        return res;
    }

    /// Computes the relative path of `toFilename` in relation to `origFilename`.
    /// If `origFilename` is already a relative path, it is returned instead. This implementation
    /// relies on [Path].
    public static String makeFilenameRelative(String origFilename, String toFilename) {
        var file = Paths.get(origFilename);
        if (!file.isAbsolute()) {
            return file.toString();
        }

        var base = Paths.get(toFilename).toAbsolutePath();
        return base.relativize(file).toString();
    }


    private static String[] removeDotDot(String[] a) {
        String[] newa = new String[a.length];
        int k = 0;
        for (int j = 0; j < a.length - 1; j++) {
            if (a[j].equals("..") || !a[j + 1].equals("..")) {
                newa[k++] = a[j];
            } else {
                j++;
            }
        }
        if (!a[a.length - 1].equals("..")) {
            newa[k++] = a[a.length - 1];
        }
        // @ assert (\forall int i; 0 <= i < k; newa[i] != null);
        // TODO: nullness. This cast cannot be checked, can it? But there is no error message
        return (String[]) Arrays.copyOf(newa, k);
    }

    public static String toValidFileName(String s) {
        s = s.replace("\\", "_").replace("$", "_").replace("?", "_").replace("|", "_")
                .replace("<", "_").replace(">", "_").replace(":", "_").replace("*", "+")
                .replace("\"", "'").replace("/", "-").replace("[", "(").replace("]", ")");
        return s;
    }

}
