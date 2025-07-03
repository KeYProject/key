/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

import java.util.concurrent.CompletableFuture;
import javax.annotation.Nullable;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

@JsonSegment("client")
public interface ClientApi {
    @JsonNotification
    void sayHello(String e);

    /**
     * LogTrace Notification (:arrow_left:)
     * A notification to log the trace of the server’s execution. The amount and content of these
     * notifications depends on the current trace configuration. If trace is 'off', the server
     * should not send any logTrace notification. If trace is 'messages', the server should not add
     * the 'verbose' field in the LogTraceParams.
     * <p>
     * $/logTrace should be used for systematic trace reporting. For single debugging messages, the
     * server should send window/logMessage notifications.
     * <p>
     * Notification:
     * <p>
     * method: ‘$/logTrace’
     * params: LogTraceParams defined as follows:
     */
    @JsonNotification
    void logTrace(LogTraceParams params);
    // region Window

    /**
     * ShowMessage Notification (:arrow_left:)
     * The show message notification is sent from a server to a client to ask the client to display
     * a particular message in the user interface.
     * <p>
     * Notification:
     * <p>
     * method: ‘window/showMessage’
     * params: ShowMessageParams defined as follows:
     */
    @JsonNotification("sm")
    void showMessage(ShowMessageParams params);



    /**
     * ShowMessage Request (:arrow_right_hook:)
     * The show message request is sent from a server to a client to ask the client to display a
     * particular message in the user interface. In addition to the show message notification the
     * request allows to pass actions and to wait for an answer from the client.
     */
    @JsonRequest
    @Nullable
    CompletableFuture<MessageActionItem> userResponse(ShowMessageRequestParams params);


    /**
     * Show Document Request (:arrow_right_hook:)
     * New in version 3.16.0
     * <p>
     * The show document request is sent from a server to a client to ask the client to display a
     * particular resource referenced by a URI in the user interface.
     * <p>
     * property path (optional): window.showDocument
     * property type: ShowDocumentClientCapabilities defined as follows:
     */
    @JsonRequest
    CompletableFuture<ShowDocumentResult> showDocument(ShowDocumentParams params);


    @JsonNotification
    void taskFinished(org.keyproject.key.api.data.TaskFinishedInfo info);

    @JsonNotification
    void taskProgress(int position);

    @JsonNotification
    void taskStarted(org.keyproject.key.api.data.TaskStartedInfo info);
    // endregion
}
