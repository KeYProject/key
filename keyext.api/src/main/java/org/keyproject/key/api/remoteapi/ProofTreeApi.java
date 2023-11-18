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
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("proofTree")
public interface ProofTreeApi {
    @JsonRequest("root")
    CompletableFuture<TreeNodeDesc> treeRoot(ProofId id);

    @JsonRequest("children")
    CompletableFuture<List<TreeNodeDesc>> treeChildren(ProofId proof, TreeNodeId nodeId);

    @JsonRequest("subtree")
    CompletableFuture<List<TreeNodeDesc>> treeSubtree(ProofId proof, TreeNodeId nodeId);
}
