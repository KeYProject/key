/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;

import org.jspecify.annotations.Nullable;


/**
 * A simple EnvInput which includes default rules and a Java path.
 */
public abstract class AbstractEnvInput implements EnvInput {

    protected final String name;
    protected final @Nullable Path javaPath;
    protected final List<Path> classPath;
    protected final @Nullable Path bootClassPath;
    protected final Includes includes;
    protected final Profile profile;

    protected InitConfig initConfig;
    private boolean ignoreOtherJavaFiles;
    private Path javaFile;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected AbstractEnvInput(String name, @Nullable Path javaPath,
            List<Path> classPath,
            @Nullable Path bootClassPath,
            Profile profile,
            List<Path> includes) {
        assert profile != null;
        this.name = name;
        this.javaPath = javaPath;
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
        this.profile = profile;
        this.includes = new Includes();
        if (includes != null) {
            for (Path path : includes) {
                this.includes.put(path.toString(), RuleSourceFactory.initRuleFile(path));
            }
        }
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public final String name() {
        return name;
    }

    @Override
    public final int getNumberOfChars() {
        return 1;
    }


    @Override
    public final void setInitConfig(InitConfig initConfig) {
        this.initConfig = initConfig;
    }


    @Override
    public final Includes readIncludes() throws ProofInputException {
        assert initConfig != null;
        return includes;
    }


    @Override
    public final Path readJavaPath() throws ProofInputException {
        return javaPath;
    }


    @Override
    public final List<Path> readClassPath() throws ProofInputException {
        return classPath;
    }


    @Override
    public Path readBootClassPath() {
        return bootClassPath;
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    public void setIgnoreOtherJavaFiles(boolean ignoreOtherJavaFiles) {
        this.ignoreOtherJavaFiles = ignoreOtherJavaFiles;
    }

    @Override
    public boolean isIgnoreOtherJavaFiles() {
        return ignoreOtherJavaFiles;
    }

    @Override
    public Path getJavaFile() {
        return javaFile;
    }

    public void setJavaFile(Path javaFile) {
        this.javaFile = javaFile;
    }
}
