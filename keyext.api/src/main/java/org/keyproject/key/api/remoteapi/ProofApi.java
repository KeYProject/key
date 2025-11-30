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
import org.keyproject.key.api.data.StrategyOptions;

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("proof")
public interface ProofApi {
    /**
     *
     * @param proofId
     * @return
     */
    @JsonRequest
    CompletableFuture<NodeDesc> root(ProofId proofId);

    /**
     * Executes the given {@code script} against the proof using the given {@code options}.
     *
     * @param proof handle of a proof
     * @param script proof script
     * @param options options towards the proof strategy
     * @return the run-time statistics
     */
    @JsonRequest
    CompletableFuture<MacroStatistic> script(ProofId proof, String script, StrategyOptions options);

    /**
     * Executes the macro given by {@code macroName} against the proof
     * using the given {@code options}.
     *
     * @param proof handle of a proof
     * @param macroName proof script
     * @param options options towards the proof strategy
     * @return the run-time statistics
     */
    @JsonRequest
    CompletableFuture<MacroStatistic> macro(ProofId proof, String macroName,
            StrategyOptions options);

    /**
     * Auto against the proof
     *
     * @param proof handle of a proof
     * @param options options towards the proof strategy
     * @return
     */
    @JsonRequest
    CompletableFuture<ProofStatus> auto(ProofId proof, StrategyOptions options);

    /**
     * Frees the resources occupied by the proof.
     *
     * @param proof
     * @return
     */
    @JsonRequest
    CompletableFuture<Boolean> dispose(ProofId proof);

    /**
     *
     * @param proof
     * @param onlyOpened
     * @param onlyEnabled
     * @return
     */
    @JsonRequest
    CompletableFuture<List<NodeDesc>> goals(ProofId proof, boolean onlyOpened, boolean onlyEnabled);

    /**
     *
     * @param proof
     * @return
     */
    @JsonRequest
    CompletableFuture<NodeDesc> tree(ProofId proof);

    /**
     *
     * @param nodeId
     * @return
     */
    @JsonRequest
    CompletableFuture<List<NodeDesc>> children(NodeId nodeId);

    /**
     * Prunes the proof branch from the leafs to the given {@code nodeId}.
     *
     * @param nodeId
     * @return
     */
    @JsonRequest
    CompletableFuture<List<NodeDesc>> pruneTo(NodeId nodeId);

    /**
     *
     * TODO
     *
     * @param proof
     * @return
     */
    @JsonRequest
    default CompletableFuture<Void> statistics(ProofId proof) {
        return CompletableFuture.completedFuture(null);
    }
}
