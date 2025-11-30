/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.ContractDesc;
import org.keyproject.key.api.data.FunctionDesc;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.SortDesc;

/**
 * The management (retrieval functions) of proof environments.
 * Using the following functions, you can obtain information of defined signature (sorts, functions,
 * etc.)
 * of an environment.
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("env")
public interface EnvApi {

    /**
     * A possible empty list of defined sorts in the environment.
     *
     * @param env a handle to the environment
     * @return a list of {@link SortDesc}
     */
    @JsonRequest
    CompletableFuture<List<SortDesc>> sorts(EnvironmentId env);

    /**
     * A possible empty list of defined functions in the environment.
     *
     * @param env a handle to the environment
     * @return a list of {@link FunctionDesc}
     */
    @JsonRequest
    CompletableFuture<List<FunctionDesc>> functions(EnvironmentId env);

    /**
     * A possible empty list of defined contracts in the environment.
     *
     * @param env a handle to the environment
     * @return a list of {@link ContractDesc}
     */
    @JsonRequest
    CompletableFuture<List<ContractDesc>> contracts(EnvironmentId env);

    /**
     * Starts a proof given by the contract handle.
     *
     * @param contractId a handle to the environment
     * @return a handle to a proof encoded as an {@link ProofId}
     */
    @JsonRequest
    CompletableFuture<ProofId> openContract(ContractId contractId);

    /**
     * This method frees the memory and datastructure of the given environment {@code env}.
     * <p>
     * After calling this method, you are not allowed t use the environment or any proof inside this
     * environment anymore.
     *
     * @param env a handle to the environment
     * @return true if the environment was dispose.
     */
    @JsonRequest
    CompletableFuture<Boolean> dispose(EnvironmentId env);
}
