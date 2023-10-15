/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.Node;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.GoalText;
import org.keyproject.key.api.data.PrintId;
import org.keyproject.key.api.data.TermAction;
import org.keyproject.key.api.data.TermActionId;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("goal")
public interface GoalApi {
    @JsonRequest
    CompletableFuture<GoalText> print(Node id);

    @JsonRequest
    CompletableFuture<List<TermAction>> actions(PrintId id, int pos);

    @JsonRequest("apply_action")
    CompletableFuture<List<TermAction>> applyAction(TermActionId id);

    @JsonNotification("free")
    void freePrint(PrintId id);
}
