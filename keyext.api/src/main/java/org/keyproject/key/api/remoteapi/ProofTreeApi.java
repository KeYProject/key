/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.Proof;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.TreeNodeDesc;
import org.keyproject.key.api.data.TreeNodeId;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("proofTree")
public interface ProofTreeApi {
    @JsonRequest("root")
    CompletableFuture<TreeNodeDesc> treeRoot(Proof id);

    @JsonRequest("children")
    CompletableFuture<List<TreeNodeDesc>> treeChildren(Proof proof, TreeNodeId nodeId);

    @JsonRequest("subtree")
    CompletableFuture<List<TreeNodeDesc>> treeSubtree(Proof proof, TreeNodeId nodeId);
}
