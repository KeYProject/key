package org.keyproject.key.api.remoteapi;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.ContractDesc;
import org.keyproject.key.api.data.FunctionDesc;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.SortDesc;

import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("env")
public interface EnvApi {
    @JsonRequest
    CompletableFuture<List<SortDesc>> sorts(EnvironmentId env);

    @JsonRequest
    CompletableFuture<List<FunctionDesc>> functions(EnvironmentId env);

    @JsonRequest
    CompletableFuture<List<ContractDesc>> contracts(EnvironmentId env);

    @JsonRequest
    CompletableFuture<ProofId> openContract(ContractId contractId);
}
