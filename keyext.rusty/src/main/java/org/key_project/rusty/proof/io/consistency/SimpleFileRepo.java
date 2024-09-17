/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io.consistency;

import java.io.*;
import java.net.JarURLConnection;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;

public class SimpleFileRepo extends AbstractFileRepo {
    @Override
    protected Path getSaveName(Path path) {
        // we have to return paths that are relative!

        Path norm = path.normalize(); // TODO: is this necessary?

        if (RUST_MATCHER.matches(norm)) { // .java
            // copy to src/classpath/bootclasspath (depending on path)
            // return getJavaFilePath(norm);
        } else if (KEY_MATCHER.matches(norm)) { // .key/.proof
            // copy to top level
            // adapt file references
            return getKeyFilePath(norm);
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
