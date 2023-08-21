/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.io.File;
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
        final char sep = File.separatorChar;
        List<String> res = new ArrayList<>();
        // if filename contains slashes, take it as UNIX filename, otherwise Windows
        if (filename.contains("/")) {
            assert sep == '/' : "\"" + filename + "\" contains both / and \\";
        } else if (filename.contains("\\")) {
            assert sep == '\\' : "\"" + filename + "\" contains both / and \\";
        } else {
            res.add(filename);
            return res;
        }
        int i = 0;
        while (i < filename.length()) {
            int j = filename.indexOf(sep, i);
            if (j == -1) { // no slash anymore
                final String s = filename.substring(i);
                if (!s.equals(".")) {
                    res.add(s);
                }
                break;
            }
            if (i == j) {
                // empty string between slashes
                if (i == 0)
                // leading slash
                {
                    res.add("");
                }
            } else {
                // contains "/./"
                final String s = filename.substring(i, j);
                if (!s.equals(".")) {
                    res.add(s);
                }
            }
            i = j + 1;
        }
        return res;
    }

    /**
     * Returns a filename relative to another one. The second parameter needs to be absolute and is
     * expected to refer to directory This method only operates on Strings, not on real files! Note
     * that it treats Strings case-sensitive. The resulting filename always uses UNIX directory
     * delimiters. Raises a RuntimeException if no relative path could be found (may happen on
     * Windows systems).
     */
    public static String makeFilenameRelative(String origFilename, String toFilename) {
        final List<String> origFileNameSections = disectFilename(origFilename);
        String[] a = origFileNameSections.toArray(new String[0]);
        final List<String> destinationFilenameSections = disectFilename(toFilename);
        String[] b =
            destinationFilenameSections.toArray(new String[0]);

        // check for Windows paths
        if (File.separatorChar == '\\' && a[0].length() == 2 && a[0].charAt(1) == ':') {
            char drive = Character.toUpperCase(a[0].charAt(0));
            if (!(b[0].length() == 2 && Character.toUpperCase(b[0].charAt(0)) == drive
                    && b[0].charAt(1) == ':')) {
                throw new RuntimeException("cannot make paths on different drives relative");
            }
            // remove drive letter
            a[0] = "";
            b[0] = "";
        }
        int i;
        StringBuilder s = new StringBuilder();
        StringBuilder t = new StringBuilder();

        if (a[0].equals("")) { // not already relative
            if (!b[0].equals("")) {
                throw new RuntimeException("\"" + toFilename
                    + "\" is a relative path. Please use absolute paths to make others relative to them.");
            }

            // remove ".." from paths
            a = removeDotDot(a);
            b = removeDotDot(b);

            // FIXME: there may be leading ..'s

            i = 1;
            boolean diff = false;
            while (i < b.length) {
                // shared until i
                if (i >= a.length || !a[i].equals(b[i])) {
                    diff = true;
                }
                // add ".." for each remaining element in b
                // and collect the remaining elements of a
                if (diff) {
                    s.append("../");
                    if (i < a.length) {
                        t.append(a[i].equals("") ? "" : "/").append(a[i]);
                    }
                }
                i++;
            }
        } else {
            i = 0;
        }
        while (i < a.length) {
            t.append(a[i].equals("") ? "" : "/").append(a[i++]);
        }
        // strip leading slash
        if (t.length() > 0 && t.charAt(0) == '/') {
            t = new StringBuilder(t.substring(1));
        }
        // strip ending slash
        t.insert(0, s);
        if (t.length() > 0 && t.charAt(t.length() - 1) == '/') {
            t = new StringBuilder(t.substring(0, t.length() - 1));
        }
        return t.toString();
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
        return Arrays.copyOf(newa, k);
    }

    public static String toValidFileName(String s) {
        s = s.replace("\\", "_").replace("$", "_").replace("?", "_").replace("|", "_")
                .replace("<", "_").replace(">", "_").replace(":", "_").replace("*", "+")
                .replace("\"", "'").replace("/", "-").replace("[", "(").replace("]", ")");
        return s;
    }

}
