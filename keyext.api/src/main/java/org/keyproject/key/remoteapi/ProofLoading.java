package org.keyproject.key.remoteapi;

import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.io.File;
import java.util.List;

@JsonSegment
public interface ProofLoading {
    @JsonRequest ProofId loadExample(String id);

    interface LoadParams {
        File keyFile;
        File javaFile;

        List<File> classPath,
        File bootClassPath, List<File> includes
    }

    /**
     * @param keyFile
     * @return
     * @throws ProblemLoaderException
     */
    @JsonRequest ProofId loadFromKeyFile(File keyFile) throws ProblemLoaderException {
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
    @JsonRequest ProofId loadProof(File location, List<File> classPath,
                                   File bootClassPath, List<File> includes) throws ProblemLoaderException {
        return new ProofManagementApi(
                KeYEnvironment.load(location, classPath, bootClassPath, includes));
    }

    /**
     * @param javaSourceCode
     * @return
     * @throws ProblemLoaderException
     */
    @JsonRequest ProofId loadProof(File javaSourceCode) throws ProblemLoaderException {
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
    @JsonRequest ProofId loadProofFile(File file, List<File> classPaths, File bootClassPath,
                                       List<File> includes);
}
