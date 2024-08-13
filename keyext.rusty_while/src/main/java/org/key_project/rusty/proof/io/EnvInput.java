/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;

import org.key_project.logic.Named;
import org.key_project.rusty.proof.init.Includes;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

public interface EnvInput extends Named {
    /**
     * Returns the total numbers of chars that can be read in this input.
     */
    int getNumberOfChars();

    /**
     * Sets the initial configuration the read environment input should be added to. Must be called
     * before calling any of the read* methods.
     */
    void setInitConfig(InitConfig initConfig);

    /**
     * Reads the include section and returns an Includes object.
     */
    Includes readIncludes() throws ProofInputException;

    /**
     * Reads the Rust path.
     */
    String readRustPath() throws ProofInputException;

    /**
     * Returns the file path to specific requested Rust file.
     */
    default @Nullable String getRustFile() throws ProofInputException {
        return null;
    }

    /**
     * Reads the input using the given modification strategy, i.e., parts of the input do not modify
     * the initial configuration while others do.
     *
     * @return The found warnings or an empty {@link ImmutableSet} if no warnings occurred.
     */
    ImmutableSet<String> read() throws ProofInputException;

    /**
     * Returns the {@link Profile} to use.
     *
     * @return The {@link Profile} to use.
     */
    Profile getProfile();

    /**
     * Returns the initial {@link File} which is loaded if available.
     *
     * @return The initial {@link File} which is loaded or {@code null} otherwise.
     */
    File getInitialFile();
}
