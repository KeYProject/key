package org.keyproject.key.api.remoteapi;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.NodeTextDesc;
import org.keyproject.key.api.data.*;
import org.keyproject.key.api.data.KeyIdentifications.*;

import java.util.List;
import java.util.concurrent.CompletableFuture;

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
