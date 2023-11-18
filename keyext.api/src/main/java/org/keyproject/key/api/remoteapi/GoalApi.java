/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.*;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.NodeTextDesc;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("goal")
public interface GoalApi {
    @JsonRequest
    CompletableFuture<NodeTextDesc> print(NodeId id, PrintOptions options);

    @JsonRequest
    CompletableFuture<List<TermActionDesc>> actions(NodeTextId id, int pos);

    @JsonRequest("apply_action")
    CompletableFuture<List<TermActionDesc>> applyAction(TermActionId id);

    @JsonNotification("free")
    void freePrint(NodeTextId id);
}
