/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.KeyIdentifications.ProofId;
import org.keyproject.key.api.data.KeyIdentifications.TreeNodeId;
import org.keyproject.key.api.data.TreeNodeDesc;

/**
 * Operations on the proof tree.
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("proofTree")
public interface ProofTreeApi {
    /**
     * Returns the node root of the tree.
     *
     * @param id
     * @return
     */
    @JsonRequest("root")
    CompletableFuture<TreeNodeDesc> treeRoot(ProofId id);

    /**
     *
     * @param proof
     * @param nodeId
     * @return
     */
    @JsonRequest("children")
    CompletableFuture<List<TreeNodeDesc>> treeChildren(ProofId proof, TreeNodeId nodeId);

    /**
     *
     * @param proof
     * @param nodeId
     *        TODO param depth
     * @return
     */
    @JsonRequest("subtree")
    CompletableFuture<List<TreeNodeDesc>> treeSubtree(ProofId proof, TreeNodeId nodeId);
}
