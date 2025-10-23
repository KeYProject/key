/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.KeYConstants;

import org.jspecify.annotations.Nullable;
import picocli.CommandLine;

public class LemmataAutoModeOptions {
    public static final int DEFAULT_TIMEOUT = -1;
    public static final int DEFAULT_MAXRULES = 10000;
    private static final String PROOF_POSTFIX = ".key.proof";

    /**
     * The path of the file containing the rules that should be proven.
     */
    @CommandLine.Option(names = "--jr-rules", paramLabel = "FILE")
    private Path pathOfRuleFile;

    /**
     * The maximum number of rules that are used within a proof.
     */
    @CommandLine.Option(names = "--jr-maxRules", paramLabel = "INT",
        description = "maximum number of rule application to perform",
        defaultValue = LemmataAutoModeOptions.DEFAULT_MAXRULES + "")
    public int maxRules = -1;

    @CommandLine.Option(names = "--jr-pathOfResult", paramLabel = "FOLDER",
        description = "store proofs to this folder")
    public @Nullable File pathOfResult = null;

    /**
     * The time out for each proof. If <code>timeout<0</code> no time out is used.
     */
    @CommandLine.Option(names = "--jr-timeout", paramLabel = "INT",
        description = "the timeout for proof of a taclet in ms",
        defaultValue = LemmataAutoModeOptions.DEFAULT_TIMEOUT + "")
    public long timeout = -1;

    @CommandLine.Option(names = "--jr-print",
        description = "send output to terminal or disable output")
    public boolean print = false;

    /**
     * If this option is activated, the resulting proofs are stored in files within the folder
     * <code>pathOfResult</code>.
     */
    @CommandLine.Option(names = "--jr-saveProofToFile",
        description = "save or drop proofs (then stored to path given by '--jr-pathOfResult')")
    public boolean saveResultsToFile = false;

    @CommandLine.Option(names = "--jr-axioms", paramLabel = "FILE",
        description = "read axioms from given file")
    public @Nullable File pathOfDefinitionFile = null;

    @CommandLine.Option(names = "--jr-signature", paramLabel = "FILE",
        description = "read definitions from given file")
    public @Nullable Path signature = null;


    private final Collection<String> filesForAxioms = new LinkedList<>();

    /**
     * Contains the internal version of KeY. It is needed for saving proofs.
     */
    private final String internalVersion;
    private final String homePath;

    public LemmataAutoModeOptions() {
        this(KeYConstants.INTERNAL_VERSION, PathConfig.getKeyConfigDir());
    }

    public LemmataAutoModeOptions(String internalVersion, String homePath) {
        this.internalVersion = internalVersion;
        this.homePath = homePath;
        checkForValidity();
    }

    public @Nullable File getPathOfDefinitionFile() {
        return pathOfDefinitionFile;
    }

    public String getHomePath() {
        return homePath;
    }

    public boolean isSavingResultsToFile() {
        return saveResultsToFile;
    }

    public Path getPathOfRuleFile() {
        return pathOfRuleFile;
    }

    public int getMaxNumberOfRules() {
        return maxRules;
    }

    public long getTimeout() {
        return timeout;
    }

    public String getInternalVersion() {
        return internalVersion;
    }

    public String createProofPath(Proof p) {
        return pathOfResult + File.separator + p.name() + PROOF_POSTFIX;
    }

    private void checkForValidity() {
        if (pathOfRuleFile != null && !Files.exists(pathOfRuleFile)) {
            throwError(String.format("Error while setting the file containing the rules:\n"
                + "'%s' is not a valid file in your system.", pathOfRuleFile));
        }

        if (pathOfResult != null && !pathOfResult.isDirectory()) {
            throwError(String.format(
                "Error while setting the folder of the results:\n'%s' is not a folder.",
                pathOfResult));
        }

    }

    private void throwError(String error) {
        throw new IllegalArgumentException(error);
    }

    public String toString() {
        return String.format(
            """
                    path of rule file: %s
                    path of result: %s
                    maximum number of rules: %s
                    timeout: %s
                    save proof to file: %s""",
            pathOfRuleFile, pathOfResult, maxRules, timeout, saveResultsToFile);
    }

    public Collection<String> getFilesForAxioms() {
        return filesForAxioms;
    }


}
