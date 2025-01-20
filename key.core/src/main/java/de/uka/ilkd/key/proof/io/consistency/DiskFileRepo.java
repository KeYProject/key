/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.*;
import java.net.JarURLConnection;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.HashMap;

import de.uka.ilkd.key.settings.GeneralSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class uses a temporary directory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public final class DiskFileRepo extends AbstractFileRepo {
    private static final Logger LOGGER = LoggerFactory.getLogger(DiskFileRepo.class);

    /**
     * The temporary directory used as a cache.
     */
    private Path tmpDir;

    /**
     * Stores for each requested path the mapping to its concrete path in repo. Key and value paths
     * are absolute, and even more, they are real paths.
     */
    private HashMap<Path, Path> map = new HashMap<>();

    /**
     * Initializes a new empty DiskFileRepo. This creates a new temporary directory.
     *
     * @param proofName name of the proof (used in the naming of the temporary directory)
     * @throws IOException if an I/O error occurs, e.g. the user has not the right to create the new
     *         temporary directory
     */
    public DiskFileRepo(String proofName) throws IOException {
        tmpDir = Files.createTempDirectory(proofName);

        // hook for deleting tmpDir + content at program exit
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            try {
                // delete the temporary directory with all contained files
                deleteDiskContent();
            } catch (IOException e) {
                // this is called at program exist, so we only print a console message
                LOGGER.info("Failed to delete tmp", e);
            }
        }));
    }

    ///////////////////////////////////////////////////////////////////////////////////////
    //////////////////// methods for loading files and opening streams ////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////

    @Override
    public InputStream getInputStream(URL url) throws IOException {
        String protocol = url.getProtocol();
        // currently, we support only two protocols: file and zip/jar
        if (protocol.equals("file")) {
            // url.getPath() may contain escaped characters -> we have to decode it
            // String path = URLDecoder.decode(url.getPath(), StandardCharsets.UTF_8.name());

            try {
                return copyAndOpenInputStream(Paths.get(url.toURI()));
            } catch (URISyntaxException e) {
                throw new IOException(e);
            }
        } else if (protocol.equals("jar")) {
            JarURLConnection juc = (JarURLConnection) url.openConnection();
            Path jarPath = Paths.get(juc.getJarFile().getName());

            if (isInternalResource(url)) {
                // do not copy anything, just establish the mapping
                map.put(jarPath, jarPath);
            } else {
                // copy the actual resource, but return an InputStream to the copy:
                // - copy resource from URL to repo
                // - add map entry URL -> file in repo
                // - return InputStream to copy
                // TODO: add private method registerPath or similar
                getInputStream(jarPath).close();
            }
            Path jarCopy = map.get(jarPath);

            // we have to create the URL as string:
            String entryStr = "jar:file:///" + jarCopy.toString() + "!/" + juc.getEntryName();
            URL entryURL = new URL(entryStr);

            return entryURL.openStream();
        } else {
            LOGGER.debug("This type of URL is not supported by the FileRepo!"
                + " Resource will not be copied to FileRepo!");
            return url.openStream(); // fallback without a copy
        }
    }

    private InputStream copyAndOpenInputStream(Path path) throws IOException {
        // this method assumes that the path exists and is a valid (w/o protocol part as in URL!)

        final Path norm = path.toAbsolutePath().normalize();

        // map lookup if the current path was already requested
        final Path p = map.get(norm);
        if (p != null) {
            return new FileInputStream(p.toFile());
        }

        // internal files are not copied to repo (but added to map for faster lookup)
        if (isInternalFile(norm)) {
            // generate map entry
            map.put(norm, norm);

            // directly return an InputStream to the file
            return new FileInputStream(norm.toFile());
        }

        if (JAVA_MATCHER.matches(norm)) { // .java
            // copy to src/classpath/bootclasspath (depending on path)
            return getJavaFileInputStream(norm);
        } else if (KEY_MATCHER.matches(norm)) { // .key/.proof
            // copy to top level
            // adapt file references
            return getKeyFileInputStream(norm);
        } else if (ZIP_MATCHER.matches(norm)) { // .zip/.jar
            // extract to classpath folder (new folder with archive name)
            return getZipFileInputStream(norm);
        } else if (CLASS_MATCHER.matches(norm)) { // .class
            // copy to classpath
            return getClassFileInputStream(norm);
        }

        // Some code relies on this method returning null, not an exception
        return null;
    }

    private InputStream getJavaFileInputStream(Path javaFile) throws IOException {
        // assumes that javaFile is an actual *.java file, path has to be absolute and normalized

        Path newFile = null;

        // Where is the file located (src, classpath, bootclasspath)?
        if (isInJavaPath(javaFile)) { // src
            newFile = resolveAndCopy(javaFile, getJavaPath(), Paths.get("src"));
        } else if (isInBootClassPath(javaFile)) { // bootclasspath
            newFile = resolveAndCopy(javaFile, getBootclasspath(), Paths.get("bootclasspath"));
        } else if (getClasspath() != null) { // classpath
            // search for matching classpath in the list
            for (Path cp : getClasspath()) {
                if (javaFile.startsWith(cp)) { // only consider directories in classpath
                    // cp is always a directory
                    // -> we put the file into the corresponding subdir in our classpath folder
                    Path parent = cp.getParent();

                    // we found the file location, so copy it
                    newFile = resolveAndCopy(javaFile, parent, Paths.get("classpath"));
                    break;
                }
            }
        }

        if (newFile != null) {
            return new FileInputStream(newFile.toFile());
        }

        return null;
    }

    private InputStream getKeyFileInputStream(Path keyFile) throws IOException {
        // compute the absolute target path (top level in repo)
        Path absTarget = tmpDir.resolve(keyFile.getFileName());

        // copy the key file to target path
        // IMPORTANT: Do not call adaptFileRefs here. This should be done when saving a repo.
        createDirsAndCopy(keyFile, absTarget);

        // register in map and list (for lookup and saving)
        map.put(keyFile, absTarget);
        addFile(keyFile);

        // return a FileInputStream to the copied file
        return new FileInputStream(absTarget.toFile());
    }

    private InputStream getZipFileInputStream(Path zipFile) throws IOException {
        // copy to classpath folder (zip/jar may only occur in classpath)
        Path newFile = resolveAndCopy(zipFile, zipFile.getParent(), Paths.get("classpath"));
        // TODO: do we really want a FileInputStream here?
        return new FileInputStream(newFile.toFile());
    }

    private InputStream getClassFileInputStream(Path classFile) throws IOException {
        // copy to classpath folder (*.class files may only occur in classpath)

        Path newFile = null;

        // class file may be in subdirectories
        // search for matching classpath in the list
        for (Path cp : getClasspath()) {
            if (classFile.startsWith(cp)) { // only consider directories in classpath
                // cp is always a directory
                // -> we put the file into the corresponding subdir in our classpath folder
                Path parent = cp.getParent();

                // we found the file location, so copy it
                newFile = resolveAndCopy(classFile, parent, Paths.get("classpath"));
                break;
            }
        }

        if (newFile != null) {
            // newFile = resolveAndCopy(classFile, classFile.getParent(), Paths.get("classpath"));
            return new FileInputStream(newFile.toFile());
        }
        return null;
    }

    // norm: absolute and normalized path of the requested file
    // containing: src, classpath, or bootclasspath folder containing norm (absolute and normalized)
    // target: src, classpath, or bootclasspath in repo (relative to repo base dir)
    private Path resolveAndCopy(Path norm, Path containing, Path relTarget) throws IOException {
        // compute relative path from containing to norm
        Path rel = containing.relativize(norm);

        // compute the absolute target path of the file in repo
        Path absTarget = tmpDir.resolve(relTarget).resolve(rel);

        // copy the old file to target path
        createDirsAndCopy(norm, absTarget);

        // register in map and list (for lookup and saving)
        map.put(norm, absTarget);
        addFile(norm);

        // return the path of the copied file
        return absTarget;
    }


    /////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////// methods for saving the repo ////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////////

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {

        if (path.isAbsolute()) {
            // programming error!
            throw new IllegalArgumentException("The path is not relative: " + path);
        }

        // store the file inside the temporary directory (relative to tmp dir)
        Path absTarget = tmpDir.resolve(path);

        // store the path translation in map
        // -> do not do this, since there exists no copy of the file except in repo
        // Path translation = baseDir.resolve(path);
        // map.put(translation, absTarget);
        addFile(path);

        return new FileOutputStream(absTarget.toFile());
    }

    @Override
    protected Path getSaveName(Path path) {
        /*
         * assumption: a file with the given path has already been stored in the repo (via
         * getInputStream() or createOutputStream())
         */

        /*
         * the given path is: 1. absolute -> lookup translation in map, relativize to tmpDir 2.
         * relative to the base dir -> nothing to do
         */

        if (path.isAbsolute()) {
            // lookup translation in map, make relative to tmpDir
            return tmpDir.relativize(map.get(path.normalize()));
        } else {
            // already relative to tmpDir
            return path;
        }
    }

    @Override
    protected InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        Path concrete;
        if (p.isAbsolute()) { // p is absolute -> lookup in map
            concrete = map.get(p.normalize());
        } else { // p is relative -> interpret as relative to tmpDir
            concrete = tmpDir.resolve(p.normalize());
        }

        if (concrete == null) {
            return null;
        }

        // open new FileInputStream of the converted path
        return new FileInputStream(concrete.toFile());
    }

    /////////////////////////////////////////////////////////////////////////////////
    //////////////////////////// methods for cleaning up ////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////

    @Override
    protected void dispose() {
        if (isDisposed()) {
            return;
        }

        try {
            // delete the temporary directory with all contained files
            deleteDiskContent();
        } catch (IOException e) {
            LOGGER.info("Failed to delete disk content", e);
        }

        // set every held reference to null
        tmpDir = null;
        map = null;
        super.dispose();
    }

    /**
     * Deletes the temporary directory with all contents (if not already done).
     *
     * @throws IOException if the directory or one of its files is not accessible
     */
    private void deleteDiskContent() throws IOException {
        if (!isDisposed() && !GeneralSettings.keepFileRepos) {
            try (var s = Files.walk(tmpDir)) {
                s.sorted(Comparator.reverseOrder())
                        // .map(Path::toFile)
                        .forEach(path -> {
                            try {
                                Files.delete(path);
                                // path.delete();
                            } catch (IOException e) {
                                LOGGER.info("Failed to delete file", e);
                            }
                        });
            }
        }
    }
}
