package de.uka.ilkd.key.proof.io.consistency;

import java.nio.file.Files;
import java.nio.file.Path;

public abstract class AbstractFileRepo implements FileRepo {
    // TODO: paths are assumed to be absolute and normalized
    /**
     * The original java source path of the repo. 
     */
    protected Path javaPath;
    protected Path classPath;
    protected Path bootClassPath;

    /**
     * The base directory of the loaded proof (needed to calculate relative paths).
     * If a .key/.proof file is loaded, this should be set to the path specified via "javaSource".
     * If a directory is loaded, baseDir should be set to the path of the directory.
     */
    protected Path baseDir;

    /**
     * This flag indicates that the Repo and all data in it have been deleted.
     */
    protected boolean disposed = false;

    @Override
    public void setBootClassPath(Path path) {
        bootClassPath = path;
    }

    @Override
    public void setClassPath(Path path) {
        classPath = path;
    }

    @Override
    public void setJavaPath(Path path) {
        javaPath = path;
    }

    @Override
    public void setBaseDir(Path path) {
        // path can be a file or a directory
        if (Files.isDirectory(path)) {
            baseDir = path.toAbsolutePath();
        } else {
            baseDir = path.getParent().toAbsolutePath();
        }
    }

    @Override
    public Path getBaseDir() {
        return baseDir;
    }

    @Override
    public void dispose() {
        // delete all references
        javaPath = null;
        classPath = null;
        bootClassPath = null;
        baseDir = null;

        disposed = true;
    }
}
