/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.MacroStatistic;
import org.keyproject.key.api.data.NodeDesc;
import org.keyproject.key.api.data.ProofStatus;
import org.keyproject.key.api.data.StreategyOptions;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("proof")
public interface ProofApi {
    @JsonRequest
    CompletableFuture<MacroStatistic> script(ProofId proof, String scriptLine,
            StreategyOptions options);

    @JsonRequest
    CompletableFuture<MacroStatistic> macro(ProofId proof, String macroName,
            StreategyOptions options);

    @JsonRequest
    CompletableFuture<ProofStatus> auto(ProofId proof, StreategyOptions options);

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

    // @JsonRequest
    // CompletableFuture<Statistics> statistics(ProofId proof);
}
