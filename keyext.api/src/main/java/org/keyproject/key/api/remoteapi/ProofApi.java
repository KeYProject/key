/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.keyproject.key.api.data.MacroStatistic;
import org.keyproject.key.api.data.NodeDesc;
import org.keyproject.key.api.data.StreategyOptions;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public interface ProofApi {
    @JsonRequest
    CompletableFuture<MacroStatistic> script(Proof proof, String scriptLine,
            StreategyOptions options);

    @JsonRequest
    CompletableFuture<MacroStatistic> macro(Proof proof, String macroId, StreategyOptions options);

    @JsonRequest
    CompletableFuture<MacroStatistic> auto(Proof proof, StreategyOptions options);

    @JsonRequest
    CompletableFuture<Boolean> dispose(Proof proof);

    @JsonRequest
    CompletableFuture<NodeDesc> goals(Proof proof);

    @JsonRequest
    CompletableFuture<NodeDesc> tree(Proof proof);

    @JsonRequest
    CompletableFuture<NodeDesc> root(Proof proof);

    @JsonRequest
    CompletableFuture<List<NodeDesc>> children(Proof proof, Node nodeId);

    @JsonRequest
    CompletableFuture<List<NodeDesc>> pruneTo(Proof proof, Node nodeId);

    @JsonRequest
    CompletableFuture<Statistics> statistics(Proof proof);
}
