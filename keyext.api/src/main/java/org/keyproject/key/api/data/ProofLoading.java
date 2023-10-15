package org.keyproject.key.api.data;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.util.concurrent.CompletableFuture;

/**
 * Functionalities for loading proofs either from a built-in example, or from a set of files.
 *
 * @author Alexander Weigl
 * @since v1
 */
@JsonSegment("loading")
public interface ProofLoading {
    /**
     * I am not sure whether this is helpful. Mainly a feature for testing?!
     * @param id
     * @return
     */
    @JsonRequest
    CompletableFuture<Proof> loadExample(String id);

    /**
     *
     */
    @JsonRequest
    CompletableFuture<Proof> loadProblem(ProblemDefinition problem);

    /**
     * Test!
     *
     * @param params parameters for loading
     * @return
     * @throws ProblemLoaderException if something went wrong
     */
    @JsonRequest
    CompletableFuture<KeYEnvironment<?>> load(LoadParams params) throws ProblemLoaderException;
}