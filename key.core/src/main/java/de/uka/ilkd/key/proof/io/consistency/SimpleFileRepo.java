/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.*;
import java.net.JarURLConnection;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * This FileRepo is able to build a proof bundle but is not able to guarantee consistency between
 * the saved proof and the source code because it does not cache the source code.
 *
 * @author Wolfram Pfeifer
 */
public class SimpleFileRepo extends AbstractFileRepo {
    @Override
    protected Path getSaveName(Path path) {
        // we have to return paths that are relative!

        Path norm = path.normalize(); // TODO: is this necessary?

        if (JAVA_MATCHER.matches(norm)) { // .java
            // copy to src/classpath/bootclasspath (depending on path)
            return getJavaFilePath(norm);
        } else if (KEY_MATCHER.matches(norm)) { // .key/.proof
            // copy to top level
            // adapt file references
            return getKeyFilePath(norm);
        } else if (ZIP_MATCHER.matches(norm)) { // .zip/.jar
            // extract to classpath folder (new folder with archive name)
            return getZipFilePath(norm);
        } else if (CLASS_MATCHER.matches(norm)) { // .class
            // copy to classpath
            return getClassFilePath(norm);
        }
        return null;
    }

    private Path getJavaFilePath(Path javaFile) {
        // assumes that javaFile is an actual *.java file, path has to be absolute and normalized
        // return value: the path of the file relative to its proof bundle root

        // Where is the file located (src, classpath, bootclasspath)?
        if (isInJavaPath(javaFile)) { // src

            Path rel = getJavaPath().relativize(javaFile);
            return Paths.get("src").resolve(rel);
        } else if (isInBootClassPath(javaFile)) { // bootclasspath
            Path rel = getBootclasspath().relativize(javaFile);
            return Paths.get("bootclasspath").resolve(rel);
        } else if (getClasspath() != null) { // classpath
            // search for matching classpath in the list
            for (Path cp : getClasspath()) {
                if (javaFile.startsWith(cp)) { // only consider directories in classpath
                    // cp is always a directory
                    Path parent = cp.getParent();

                    Path rel = parent.relativize(javaFile);
                    return Paths.get("classpath").resolve(rel);
                }
            }
        }

        return null;
    }

    private Path getKeyFilePath(Path keyFile) {
        if (keyFile.isAbsolute()) {
            // compute the relative target path (top level in repo)
            return getBaseDir().relativize(keyFile);
        } else {
            // already relative to top level in repo
            return keyFile;
        }
    }

    private Path getZipFilePath(Path zipFile) {
        // zip/jar may only occur in classpath
        Path rel = zipFile.getFileName();
        return Paths.get("classpath").resolve(rel);
    }

    private Path getClassFilePath(Path classFile) {
        // copy to classpath folder (*.class files may only occur in classpath)

        // class file may be in subdirectories
        // search for matching classpath in the list
        for (Path cp : getClasspath()) {
            if (classFile.startsWith(cp)) { // only consider directories in classpath
                // cp is always a directory
                // -> we put the file into the corresponding subdir in our classpath folder
                Path parent = cp.getParent();

                // we found the file location
                Path rel = parent.resolve(classFile);
                return Paths.get("classpath").resolve(rel);
            }
        }

        return null;
    }

    @Override
    protected InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        Path concrete;
        if (p.isAbsolute()) { // p is absolute -> directly read
            concrete = p.normalize();
        } else { // p is relative -> interpret as relative to baseDir
            concrete = getBaseDir().resolve(p.normalize());
        }

        if (concrete == null) {
            return null;
        }

        // open new FileInputStream of the converted path
        return new FileInputStream(concrete.toFile());
    }

    @Override
    public InputStream getInputStream(URL url) throws IOException {
        String protocol = url.getProtocol();

        // currently, we support only two protocols: file and zip/jar
        if (protocol.equals("file")) {
            // url.getPath() may contain escaped characters -> we have to decode it
            // String path = URLDecoder.decode(url.getPath(), StandardCharsets.UTF_8.name());

            try {
                Path path = Paths.get(url.toURI());
                return copyAndOpenInputStream(path);
            } catch (URISyntaxException e) {
                throw new IOException("The given URL is invalid!", e);
            }

        } else if (protocol.equals("jar")) {
            JarURLConnection juc = (JarURLConnection) url.openConnection();
            Path jarPath = Paths.get(juc.getJarFile().getName());
            addFile(jarPath);
            return url.openStream();
        } else {
            throw new IOException("This type of URL is not supported!");
        }
    }

    private InputStream copyAndOpenInputStream(Path path) throws IOException {
        // this method assumes that the path exists and is a valid path
        // (w/o protocol part as in URL!)

        final Path norm = path.toAbsolutePath().normalize();

        // internal files are not registered to repo
        if (!isInternalFile(norm)) {
            addFile(norm);
        }

        return new FileInputStream(norm.toFile());
    }

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {
        if (path.isAbsolute()) {
            // programming error!
            throw new IllegalArgumentException("The path is not relative: " + path);
        }

        // store the file relative to base dir
        Path absTarget = getBaseDir().resolve(path);
        addFile(path);

        // TODO: This silently creates files in the baseDir of the FileRepo!
        return new FileOutputStream(absTarget.toFile());
    }
}
