// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

import java.io.File;
import java.io.IOException;
import java.util.StringTokenizer;

/**
 * @author AL
 * @author UH (extension class localization)
 */
public class FileUtils {

    private static File userDirectory;

    public static File getUserDirectory() {
        if (userDirectory == null) {
            userDirectory = new File(System.getProperty("user.dir"));
        }
        return userDirectory;
    }

    /*
     * If the start is not a directory, the start is set to it's parent. If no
     * canonical path for the destination is available, the absolute path is
     * chosen. If the start and destination are equal, "." is returned. If start
     * and destination have no common prefix, they are in different root
     * directories (or devices) and the full path to the destination is
     * returned.
     */
    public static String getRelativePath(File start, File dest) {
        if (start.isFile()) {
            start = new File(start.getParent());
        }
        String startname;
        String destname;
        try {
            startname = start.getCanonicalPath();
            destname = dest.getCanonicalPath();
        } catch (IOException ioe) {
            return dest.getAbsolutePath();
        }
        if (startname.equals(destname)) {
            return ".";
        }
        int slen = startname.length();
        int dlen = destname.length();
        int maxlen = Math.min(slen, dlen);
        int index;
        for (index = 0; index < maxlen; index += 1) {
            if (startname.charAt(index) != destname.charAt(index)) {
                break;
            }
        }
        if (index <= 1) {
            // no common header: different devices; use absolute path
            return destname;
        }
        StringBuffer result = new StringBuffer();
        if (index != slen) {
            while (index > 0 && (startname.charAt(index) != File.separatorChar)) {
                index -= 1;
            }
            index += 1;
            result.append("..").append(File.separatorChar);
            for (int dirs = index; dirs < slen; dirs += 1) {
                if (startname.charAt(dirs) == File.separatorChar) {
                    result.append("..").append(File.separatorChar);
                }
            }
        } else {
            index += 1;
        }
        if (index < dlen) {
            result.append(destname.substring(index));
        }
        return result.toString();
    }

    private final static String ARCHIVE_NAME;

    static {
        if (System.getProperty("java.version").startsWith("1.1")) {
            ARCHIVE_NAME = "classes.zip";
        } else {
            ARCHIVE_NAME = "rt.jar";
        }
    }

    /**
     * Returns the file representing the Java system class archive file, if it
     * exists.
     * 
     * @return the Java system class archive file.
     */
    public static File getPathOfSystemClasses() {
        File result = null;
        String classpath = System.getProperty("java.class.path");
        if (classpath != null) {
            char sep = File.separatorChar;
            if (sep == '/')
                classpath = classpath.replace('\\', sep);
            else if (sep == '\\')
                classpath = classpath.replace('/', sep);
            StringTokenizer tok = new StringTokenizer(classpath, File.separator);
            while (tok.hasMoreTokens()) {
                classpath = tok.nextToken();
                if (classpath.endsWith(File.separator + ARCHIVE_NAME)) {
                    result = new File(classpath);
                    if (result.exists()) {
                        break;
                    } else {
                        result = null;
                    }
                }
            }
        }
        if (result == null) {
            classpath = System.getProperty("java.home") + File.separator + "lib" + File.separator + ARCHIVE_NAME;
            result = new File(classpath);
        }
        if (!result.exists()) {
            result = null;
        }
        return result;
    }

    /**
     * Returns the magic ext directory.
     * 
     * @return the Java system class archive file.
     * @since 0.72
     */
    public static File getPathOfExtensionClassesDir() {
        File result = null;
        String classpath = System.getProperty("java.home") + File.separator + "lib" + File.separator + "ext";

        result = new File(classpath);
        if (!result.exists()) {
            result = null;
        }
        return result;
    }

    public static void main(String[] a) throws IOException {
        System.out.println("Current directory is " + getUserDirectory());
        if (a.length > 0) {
            File f = new File(a[0]);
            System.out.println("File is " + f.getCanonicalPath());
            if (f.exists()) {
                System.out.println("Relative path is " + getRelativePath(getUserDirectory(), f));
            }
        }
    }
}