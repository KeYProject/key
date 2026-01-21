// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.io.File;
import java.io.FilenameFilter;

/**
 * Convenience class to collect all files of a directory tree, recursively. The
 * collection obeys the following rules:
 * <OL>
 * <LI>If a name corresponds to a file, it is reported.
 * <LI>If a name corresponds to a non-existing file, nothing is reported.
 * <LI>If a name corresponds to a directory, the directory itself is not
 * reported, but all files in it, following rules 1-3. This will lead to a
 * recursive collection of all files in all subdirectories.
 * </OL>
 * 
 * @author AL
 */
public class FileCollector {

    private File[] stack;

    private File current;

    private int count;

    /**
     * Create a file collector starting with the given filename.
     */
    public FileCollector(String root) {
        this(new File(root));
    }

    /**
     * Create a file collector starting with the given file.
     */
    public FileCollector(File root) {
        stack = new File[8];
        stack[count++] = root;
    }

    /**
     * For internal use. Double stack.
     */
    private void growStack() {
        File[] newStack = new File[stack.length * 2];
        System.arraycopy(stack, 0, newStack, 0, count);
        stack = newStack;
    }

    /**
     * Proceed to the next file and return if this has been possible.
     * 
     * @return true iff there is a next file available for {@link #getFile()}.
     */
    public boolean next() {
        outer: while (count > 0) {
            current = stack[--count]; // pop
            while (current.isDirectory()) {
                String[] content = current.list();
                for (int i = content.length - 1; i >= 0; i -= 1) {
                    stack[count++] = new File(current, content[i]); // push
                    if (count == stack.length) {
                        growStack();
                    }
                }
                if (count == 0) {
                    break outer;
                }
                current = stack[--count]; // pop
            }
            if (current.exists()) {
                return true;
            }
        }
        current = null;
        return false;
    }

    /**
     * Proceed to the next file with the given suffix and return if this has
     * been possible. Remember to include the dot in the suffix (".java", not
     * "java").
     * 
     * @return true iff there is a next file with the given extension available
     *         for {@link #getFile()}.
     */
    public boolean next(String suffix) {
        while (next()) {
            if (current.getName().endsWith(suffix)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Proceed to the next file that is accepted by the given filter and return
     * if this has been possible.
     * 
     * @return true iff there is a next file available for {@link #getFile()}
     *         that is accepted by the filter.
     */
    public boolean next(FilenameFilter filter) {
        String pname = "";
        File pfile = null;
        while (next()) {
            String p = current.getParent();
            if (p == null) {
                p = "";
            }
            if (!pname.equals(p)) {
                pname = p;
                pfile = new File(pname);
            }
            if (filter.accept(pfile, current.getName())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Fetch the current file, or null if no one is available.
     * 
     * @return the current file, or null if {@link #next()}has not been called
     *         before or returned false.
     */
    public File getFile() {
        return current;
    }

    /*
     * Sample program printing out all .java files available from the location
     * as stated by the first argument.
     * 
     * public static void main(String[] a) throws IOException { if (a.length !=
     * 1) { System.err.println("Try it with a single argument."); }
     * FileCollector me = new FileCollector(a[0]); while (me.next(".java")) {
     * File f = me.getFile(); System.out.println(f.getName()); } }
     */
}