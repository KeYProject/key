package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

@JsonSegment
public interface ProofLoading {
    @JsonRequest
    ProofId loadExample(String id);

    /**
     * @param params
     * @return
     * @throws ProblemLoaderException
     */
    @JsonRequest
    EnvId load(LoadParams params) throws ProblemLoaderException;
}