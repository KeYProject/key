package de.uka.ilkd.key.proof.io;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;


/**
 * A simple EnvInput which includes default rules and a Java path.
 */
public abstract class AbstractEnvInput implements EnvInput {

    protected final String name;
    protected final Path javaPath;
    protected final List<Path> classPath;
    protected final Path bootClassPath;
    protected final Includes includes;
    protected final Profile profile;

    protected InitConfig initConfig;
    private boolean ignoreOtherJavaFiles;
    private Path javaFile;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public AbstractEnvInput(String name, Path javaPath, List<Path> classPath, Path bootClassPath,
            Profile profile, List<Path> includes) {
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
    public final Includes readIncludes() {
        assert initConfig != null;
        return includes;
    }


    @Override
    public final @Nonnull Optional<Path> readJavaPath() {
        return Optional.ofNullable(javaPath);
    }


    @Nonnull
    @Override
    public final Optional<List<Path>> readClassPath() {
        return Optional.ofNullable(classPath);
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
