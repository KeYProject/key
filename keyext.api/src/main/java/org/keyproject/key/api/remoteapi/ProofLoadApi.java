/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.KeyIdentifications.EnvironmentId;
import org.keyproject.key.api.data.KeyIdentifications.ProofId;
import org.keyproject.key.api.data.LoadParams;
import org.keyproject.key.api.data.ProblemDefinition;

/**
 * Functionalities for loading proofs either from a built-in example, or from a set of files.
 *
 * @author Alexander Weigl
 * @since v1
 */
@JsonSegment("loading")
public interface ProofLoadApi {

    /**
     *
     * @param problem
     * @return
     */
    @JsonRequest
    CompletableFuture<ProofId> loadProblem(ProblemDefinition problem);

    /**
     *
     * @param content
     * @return
     */
    @JsonRequest
    CompletableFuture<ProofId> loadKey(String content);

    /**
     *
     * @param term
     * @return
     */
    @JsonRequest
    CompletableFuture<ProofId> loadTerm(String term);

    /**
     * Test!
     *
     * @param params parameters for loading
     * @return
     * @throws ProblemLoaderException if something went wrong
     */
    @JsonRequest
    CompletableFuture<Either<EnvironmentId, ProofId>> load(LoadParams params)
            throws ProblemLoaderException;
}
