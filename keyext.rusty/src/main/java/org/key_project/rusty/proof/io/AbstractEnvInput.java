/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;
import java.util.List;

import org.key_project.logic.Name;
import org.key_project.rusty.proof.init.Includes;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;

import org.jspecify.annotations.NonNull;

public abstract class AbstractEnvInput implements EnvInput {
    protected final Name name;
    protected final String rustPath;
    protected final Includes includes;
    protected final Profile profile;

    protected InitConfig initConfig;
    private String rustFile;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public AbstractEnvInput(String name, String rustPath,
            Profile profile, List<File> includes) {
        assert profile != null;
        this.name = new Name(name);
        this.rustPath = rustPath;
        this.profile = profile;
        this.includes = new Includes();
        if (includes != null) {
            for (File path : includes) {
                this.includes.put(path.toString(), RuleSourceFactory.initRuleFile(path));
            }
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public final @NonNull Name name() {
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
    public final String readRustPath() throws ProofInputException {
        return rustPath;
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public String getRustFile() {
        return rustFile;
    }

    public void setRustFile(String rustFile) {
        this.rustFile = rustFile;
    }
}
