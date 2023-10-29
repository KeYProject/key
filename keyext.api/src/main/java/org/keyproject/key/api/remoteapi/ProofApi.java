package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.proof.Statistics;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.MacroStatistic;
import org.keyproject.key.api.data.NodeDesc;
import org.keyproject.key.api.data.StreategyOptions;

import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public interface ProofApi {
    @JsonRequest
    CompletableFuture<MacroStatistic> script(ProofId proof, String scriptLine, StreategyOptions options);

    @JsonRequest
    CompletableFuture<MacroStatistic> macro(ProofId proof, String macroId, StreategyOptions options);

    @JsonRequest
    CompletableFuture<MacroStatistic> auto(ProofId proof, StreategyOptions options);

    @JsonRequest
    CompletableFuture<Boolean> dispose(ProofId proof);

    @JsonRequest
    CompletableFuture<List<NodeDesc>> goals(ProofId proof, boolean onlyOpened, boolean onlyEnabled);

    @JsonRequest
    CompletableFuture<NodeDesc> tree(ProofId proof);

    @JsonRequest
    CompletableFuture<NodeDesc> root(ProofId proof);

    @JsonRequest
    CompletableFuture<List<NodeDesc>> children(NodeId nodeId);

    @JsonRequest
    CompletableFuture<List<NodeDesc>> pruneTo(NodeId nodeId);

    @JsonRequest
    CompletableFuture<Statistics> statistics(ProofId proof);
}
