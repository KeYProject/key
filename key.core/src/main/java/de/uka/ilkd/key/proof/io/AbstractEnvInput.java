/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.proof.init.*;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * A simple EnvInput which includes default rules and a Java path.
 */
@NullMarked
public abstract class AbstractEnvInput implements EnvInput {

    protected final String name;
    protected final @Nullable Path javaPath;
    protected final List<Path> classPath;
    protected final @Nullable Path bootClassPath;
    protected final Includes includes;
    protected final @Nullable Profile profile;

    protected InitConfig initConfig;
    private boolean ignoreOtherJavaFiles;
    private @Nullable Path javaFile;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * The {@link InitConfig} is bound later by the loader via {@link #setInitConfig(InitConfig)}
     * once the environment is built; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    protected AbstractEnvInput(String name, @Nullable Path javaPath,
            List<Path> classPath,
            @Nullable Path bootClassPath,
            @Nullable Profile profile,
            @Nullable List<Path> includes) {
        this.name = name;
        this.javaPath = javaPath;
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
        if (profile != null) {
            this.profile = profile;
        } else {
            this.profile = JavaProfile.getDefaultProfile();
        }
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
    public final @Nullable Path readJavaPath() throws ProofInputException {
        return javaPath;
    }


    @Override
    public final List<Path> readClassPath() {
        return classPath;
    }


    @Override
    public @Nullable Path readBootClassPath() {
        return bootClassPath;
    }

    @Override
    public Profile getProfile() {
        Profile result = profile;
        if (result == null) {
            throw new IllegalStateException("The input provides no profile");
        }
        return result;
    }

    public void setIgnoreOtherJavaFiles(boolean ignoreOtherJavaFiles) {
        this.ignoreOtherJavaFiles = ignoreOtherJavaFiles;
    }

    @Override
    public boolean isIgnoreOtherJavaFiles() {
        return ignoreOtherJavaFiles;
    }

    @Override
    public @Nullable Path getJavaFile() {
        return javaFile;
    }

    public void setJavaFile(Path javaFile) {
        this.javaFile = javaFile;
    }
}
