package de.uka.ilkd.key.proof.io.consistency;

import java.nio.file.Path;

public abstract class AbstractFileRepo implements FileRepo {
    // TODO: paths are assumed to be absolute and normalized
    /**
     * The original java source path of the repo. 
     */
    protected Path javaPath;
    protected Path classPath;
    protected Path bootClassPath;

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
}
