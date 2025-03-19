/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.KeYConstants;

/**
 * The Entry Point.
 * <p>
 * This facility is the entry point to the different KeY apis. Currently it support the
 * bootstrapping of the {@link KeYEnvironment} and the loading of proofs.
 * <p>
 * Created at 6.4.17
 *
 * @author Sarah Grebing
 * @author Alexander Weigl
 * @see ProofScriptCommandApi
 */
public abstract class KeYApi {
    private static final ProofMacroApi proofMacroApi = new ProofMacroApi();
    private static final ProofScriptCommandApi scriptCommandApi = new ProofScriptCommandApi();

    /**
     * Create a new KeY API and create the sub APIs
     */
    private KeYApi() {
    }

    /**
     *
     * @return
     */
    public static String getVersion() {
        return KeYConstants.INTERNAL_VERSION;
    }


    /**
     * @return non-null
     */
    public static ProofScriptCommandApi getScriptCommandApi() {
        return scriptCommandApi;
    }

    /**
     * @return a non-null references to the macro api
     */
    public static ProofMacroApi getMacroApi() {
        return proofMacroApi;
    }

    /**
     * @param keyFile
     * @return
     * @throws ProblemLoaderException
     */
    public static ProofManagementApi loadFromKeyFile(File keyFile) throws ProblemLoaderException {
        return new ProofManagementApi(KeYEnvironment.load(keyFile));
    }

    /**
     * @param location
     * @param classPath
     * @param bootClassPath
     * @param includes
     * @return
     * @throws ProblemLoaderException
     */
    public static ProofManagementApi loadProof(File location, List<File> classPath,
            File bootClassPath, List<File> includes) throws ProblemLoaderException {
        return new ProofManagementApi(
            KeYEnvironment.load(location, classPath, bootClassPath, includes));
    }

    /**
     * @param javaSourceCode
     * @return
     * @throws ProblemLoaderException
     */
    public static ProofManagementApi loadProof(File javaSourceCode) throws ProblemLoaderException {
        return loadProof(javaSourceCode, null, null, null);
    }

    /**
     * Load a proof file, creates a KeY environment that can be accessed with other methods from
     * this facade
     *
     * @param file Path to the source code folder/file or to a *.proof file
     * @param classPaths Optionally: Additional specifications for API classes
     * @param bootClassPath Optionally: Different default specifications for Java API
     * @param includes Optionally: Additional includes to consider
     */
    public abstract void loadProofFile(File file, List<File> classPaths, File bootClassPath,
            List<File> includes);

}
