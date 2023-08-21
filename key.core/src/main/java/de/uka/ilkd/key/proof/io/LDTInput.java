/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


/**
 * Represents the LDT .key files as a whole. Special treatment of these files is necessary because
 * their parts need to be read in a special order, namely first all sort declarations then all
 * function and predicate declarations and third the rules. This procedure makes it possible to use
 * all declared sorts in all rules.
 */
public class LDTInput implements EnvInput {
    public interface LDTInputListener {
        void reportStatus(String status, int progress);
    }

    private static final String NAME = "language data types";

    private final KeYFile[] keyFiles;
    private final LDTInputListener listener;
    private final Profile profile;

    private InitConfig initConfig = null;

    /**
     * creates a representation of the LDT files to be used as input to the KeY prover.
     *
     * @param keyFiles an array containing the LDT .key files
     * @param main the main class used to report the progress of reading
     */
    public LDTInput(KeYFile[] keyFiles, LDTInputListener listener, Profile profile) {
        assert profile != null;
        this.keyFiles = keyFiles;
        this.listener = listener;
        this.profile = profile;
    }


    @Override
    public String name() {
        return NAME;
    }


    @Override
    public int getNumberOfChars() {
        int sum = 0;
        for (KeYFile keyFile : keyFiles) {
            sum = sum + keyFile.getNumberOfChars();
        }
        return sum;
    }


    @Override
    public void setInitConfig(InitConfig conf) {
        this.initConfig = conf;
        for (KeYFile keyFile : keyFiles) {
            keyFile.setInitConfig(conf);
        }
    }


    @Override
    public Includes readIncludes() throws ProofInputException {
        Includes result = new Includes();
        for (KeYFile keyFile : keyFiles) {
            result.putAll(keyFile.readIncludes());
        }
        return result;
    }


    @Override
    public String readJavaPath() throws ProofInputException {
        return "";
    }


    // no class path elements here
    @Override
    public List<File> readClassPath() throws ProofInputException {
        return null;
    }


    // no class path elements here
    @Override
    public File readBootClassPath() {
        return null;
    }


    /**
     * reads all LDTs, i.e., all associated .key files with respect to the given modification
     * strategy. Reading is done in a special order: first all sort declarations then all function
     * and predicate declarations and third the rules. This procedure makes it possible to use all
     * declared sorts in all rules, e.g.
     */
    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("LDTInput: InitConfig not set.");
        }

        for (KeYFile keYFile : keyFiles) {
            keYFile.readSorts();
        }
        for (KeYFile file : keyFiles) {
            file.readFuncAndPred();
        }
        // create LDT objects to have them available for parsing
        initConfig.getServices().getTypeConverter().init();
        for (KeYFile keyFile : keyFiles) {
            if (listener != null) {
                listener.reportStatus("Reading " + keyFile.name(),
                    keyFile.getNumberOfChars());
            }
            keyFile.readRules();
        }


        return DefaultImmutableSet.nil();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof LDTInput)) {
            return false;
        }

        LDTInput li = (LDTInput) o;
        if (keyFiles.length != li.keyFiles.length) {
            return false;
        }

        for (KeYFile keyFile : keyFiles) {
            boolean found = false;
            for (int j = 0; j < keyFiles.length; j++) {
                if (li.keyFiles[j].equals(keyFile)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }

        return true;
    }


    @Override
    public int hashCode() {
        int result = 0;
        for (KeYFile keyFile : keyFiles) {
            result += keyFile.hashCode();
        }
        return result;
    }

    @Override
    public String toString() {
        return name();
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public File getInitialFile() {
        return null;
    }
}
