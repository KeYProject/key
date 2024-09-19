/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.io.File;
import java.util.List;

import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.rusty.proof.io.AbstractEnvInput;
import org.key_project.util.collection.ImmutableSet;

public final class SLEnvInput extends AbstractEnvInput {

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public SLEnvInput(String rustPath, Profile profile,
            List<File> includes) {
        super(getLanguage() + " specifications", rustPath, profile,
            includes);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ImmutableSet<String> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }

        // TODO
        // return createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        return null;
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    public static String getLanguage() {
        return "no";
        /*
         * GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
         * if (gs.isUseJML()) {
         * return "JML";
         * } else {
         * return "no";
         * }
         */
    }

    @Override
    public File getInitialFile() {
        return null;
    }

}
