/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.*;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import recoder.util.FileCollector;
import recoder.util.StringUtils;

/**
 * This class describes a list of search paths. Search paths may contain a mixture of directories,
 * logical directories (e.g. "."), and archive files (e.g. ".jar", ".zip").
 *
 * @author RN
 * @author AL
 */
public class PathList {

    private final static File NO_FILE = new File("");
    /**
     * Caches names of types relative to the search path that are known to be unknown. Set <String>.
     */
    private final Set<String> notFound = new HashSet<>();
    /**
     * Maps filenames to data locations. Map <String, DataLocation>.
     */
    private final Map<String, DataLocation> locations = new HashMap<>();
    /**
     * Stores path entries. List <File|ZipFile>.
     */
    private final List<Object> paths = new ArrayList<>();
    /**
     * Caches directory content queries. Map <File, NaturalHashSet>.
     */
    private final Map<File, Set<String>> dirContents = new HashMap<>();
    /**
     * Caches known directories. Map <File, File>.
     */
    private final Map<File, File> knownDirs = new HashMap<>();

    /**
     * creates a new empty path list
     */
    public PathList() {
        super();
    }

    /**
     * creates a path list from the given path string
     *
     * @param pathStr a single path string, e.g. the content of <tt>CLASSPATH</tt>
     */
    public PathList(String pathStr) {
        add(pathStr);
    }

    /**
     * creates a path list from the given strings. The single strings are interpreted as path
     * strings.
     *
     * @param paths the array of path strings to be added
     */
    public PathList(String[] paths) {
        for (String path : paths) {
            add(path);
        }
    }

    /**
     * Empties the caches of this service.
     *
     * @since 0.72
     */
    public void flushCaches() {
        dirContents.clear();
        knownDirs.clear();
        notFound.clear();
    }

    private void addPath(String path) {
        File f = new File(path);
        if (f.isFile()) {
            try {
                paths.add(new ZipFile(f));
            } catch (IOException ioe) {
                /* ignore this file */
            }
        } else if (f.isDirectory()) {
            paths.add(f);
        }
    }

    /**
     * adds the given paths to the list.
     *
     * @param pathStr the string containing the paths
     * @return the number of paths added from the path string
     */
    public int add(String pathStr) {
        int result = 0;
        if (pathStr != null) {
            String[] split_paths = StringUtils.split(pathStr, File.pathSeparatorChar);
            result = split_paths.length;
            for (int i = 0; i < result; i++) {
                String path = split_paths[i].trim();
                if (!path.equals("")) {
                    addPath(path);
                }
            }
            notFound.clear(); // clear the buffer of illegal requests
        }
        return result;
    }

    /**
     * Returns a set of file names in the given directory.
     */
    protected Set getContents(File directory) {
        Set<String> result = dirContents.get(directory);
        if (result == null) {
            dirContents.put(directory, result = new HashSet<>());
            String[] list = null;
            list = directory.list();
            Collections.addAll(result, list);
        }
        return result;
    }

    private File getDir(File parent, String name) {
        File attempt = new File(parent, name);
        File result = knownDirs.get(attempt);
        if (result == null) {
            result = attempt;
            if (!result.exists()) {
                result = NO_FILE;
            }
            knownDirs.put(attempt, result);
        }
        return (result == NO_FILE) ? null : result;
    }

    private DataLocation getLocation(Object p, String relativeName) {
        if (p instanceof ZipFile) {
            ZipFile zf = (ZipFile) p;
            if (zf.getEntry(relativeName) != null) {
                return new ArchiveDataLocation(zf, relativeName);
            } else {
                // archives use unix-paths
                String hs = relativeName.replace(File.separatorChar, '/');
                if (zf.getEntry(hs) != null) {
                    return new ArchiveDataLocation(zf, hs);
                }
            }
        } else if (p instanceof File) {
            File dir = (File) p;
            int sep = relativeName.lastIndexOf(File.separatorChar);
            if (sep >= 0) {
                dir = getDir(dir, relativeName.substring(0, sep));
                if (dir == null) {
                    return null;
                }
                relativeName = relativeName.substring(sep + 1);
            }
            if (getContents(dir).contains(relativeName)) {
                return new DataFileLocation(new File(dir, relativeName));
            }
        }
        return null;
    }

    /**
     * Looks for the file with the given relative file name in the path list and returns the
     * according location object. If no such file can be found within the paths, the method returns
     * <tt>null</tt>.
     *
     * @param relativeName the relative name of the file
     * @return the location object or <tt>null</tt> if the file could not be found.
     */
    public DataLocation find(String relativeName) {
        DataLocation result = locations.get(relativeName);
        if ((result == null) && (!notFound.contains(relativeName))) {
            for (int i = 0; result == null && i < paths.size(); i++) {
                result = getLocation(paths.get(i), relativeName);
            }
            if (result != null) {
                locations.put(relativeName, result);
            } else {
                notFound.add(relativeName);
            }
        }
        return result;
    }

    /**
     * Returns a relative name of the given absolute file name removing a directory path prefix if
     * the prefix occurs in this path list. If the filename is a directory path that is already in
     * this path list, a "." is returned. In any other case, the absolute file name is passed
     * through.
     *
     * @param absoluteFilename an absolute file name.
     * @return a name for this file, possibly relative to this search path.
     */
    public String getRelativeName(String absoluteFilename) {
        for (Object o : paths) {
            if (o instanceof File) {
                File p = (File) o;
                if (p.isDirectory()) {
                    String pathfilename = p.getAbsolutePath();
                    if (absoluteFilename.startsWith(pathfilename)) {
                        int pathfilenamelen = pathfilename.length();
                        if (absoluteFilename.length() == pathfilenamelen) {
                            return ".";
                        }
                        if (pathfilename.charAt(pathfilenamelen - 1) != File.separatorChar) {
                            pathfilenamelen += 1; // cut one more
                        }
                        return absoluteFilename.substring(pathfilenamelen);
                    }
                }
            }
        }
        return absoluteFilename;
    }

    /**
     * Looks for files with the given relative file name in the path list and returns an array
     * containing the full path names of each match. If no file could be located, this method
     * returns an empty array.
     *
     * @param relativeName the relative name of the file
     * @return an array containing the full paths of all matching files
     */
    public DataLocation[] findAll(String relativeName) {
        DataLocation[] tmpRes = new DataLocation[paths.size()];
        int count = 0;
        for (Object path : paths) {
            DataLocation dl = getLocation(path, relativeName);
            if (dl != null) {
                tmpRes[count++] = dl;
            }
        }
        // create the result array
        DataLocation[] result = new DataLocation[count];
        System.arraycopy(tmpRes, 0, result, 0, count);
        return result;
    }

    // the filter must be able to accept null parent directories
    // (e.g. for ZipEntries)
    public DataLocation[] findAll(FilenameFilter filter) {
        List<DataLocation> res = new ArrayList<>();
        for (Object f : paths) {
            if (f instanceof ZipFile) {
                ZipFile zf = (ZipFile) f;
                Enumeration enum2 = zf.entries();
                while (enum2.hasMoreElements()) {
                    ZipEntry e = (ZipEntry) enum2.nextElement();
                    String name = e.getName();
                    if (filter.accept(null, name)) {
                        DataLocation loc = locations.get(name);
                        if (loc == null) {
                            loc = new ArchiveDataLocation(zf, name);
                            locations.put(name, loc);
                        }
                        res.add(loc);
                    }
                }
            } else {
                File fi = (File) f;
                if (fi.exists()) {
                    FileCollector fc = new FileCollector(fi);
                    while (fc.next(filter)) {
                        File file = fc.getFile();
                        try {
                            String name = file.getCanonicalPath();
                            DataLocation loc = locations.get(name);
                            if (loc == null) {
                                loc = new DataFileLocation(file);
                                locations.put(name, loc);
                            }
                            res.add(loc);
                        } catch (IOException ioe) {
                        }
                    }
                }
            }
        }
        DataLocation[] result = new DataLocation[res.size()];
        res.toArray(result);
        return result;
    }

    /**
     * Returns the string representation of the path list.
     *
     * @return the concatenated pathstring.
     */
    public String toString() {
        String result;
        if (paths.isEmpty()) {
            result = "";
        } else {
            StringBuilder sb = new StringBuilder();
            for (Object path : paths) {
                sb.append(File.pathSeparatorChar);
                Object f = path;
                if (f instanceof ZipFile) {
                    sb.append(((ZipFile) f).getName());
                } else {
                    sb.append(((File) f).getPath());
                }
            }
            result = sb.substring(1);
        }
        return result;
    }

}
