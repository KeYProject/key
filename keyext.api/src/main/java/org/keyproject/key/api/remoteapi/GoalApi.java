/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.KeyIdentifications.NodeId;
import org.keyproject.key.api.data.KeyIdentifications.NodeTextId;
import org.keyproject.key.api.data.KeyIdentifications.TermActionId;
import org.keyproject.key.api.data.NodeTextDesc;
import org.keyproject.key.api.data.PrintOptions;
import org.keyproject.key.api.data.TermActionDesc;

/**
 * Working with goals: This includes the applications of rules, macros and user interaction to
 * sequents.
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("goal")
public interface GoalApi {
    /**
     * Prints the sequent of the given node using the given {@code options}.
     *
     * @param id a handle of a node
     * @param options printing options
     * @return the printed sequent
     */
    @JsonRequest
    CompletableFuture<NodeTextDesc> print(NodeId id, PrintOptions options);

    /**
     * Finds possible actions for the print-out given handle {@code id} and the
     * textual positon {@code pos}. Caret position starts with 0.
     *
     * @param id handle
     * @param caretPos position inside the print-out (0<= pos < text_length)
     * @return a list of possible actions that can be invoked at the caret position.
     */
    @JsonRequest
    CompletableFuture<List<TermActionDesc>> actions(NodeTextId id, int caretPos);

    /**
     * Applies the given action identify by {@code id}.
     *
     * @param id a handle to a term action
     * @return true
     */
    @JsonRequest("apply_action")
    CompletableFuture<Boolean> applyAction(TermActionId id);

    /**
     * Frees the privious occupied print-out of a sequent.
     *
     * @param id
     */
    @JsonNotification("free")
    void freePrint(NodeTextId id);
}
