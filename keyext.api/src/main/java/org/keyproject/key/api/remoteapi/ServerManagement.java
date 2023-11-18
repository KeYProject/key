/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.TraceValue;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("server")
public interface ServerManagement {
    /**
     * Shutdown Request (:leftwards_arrow_with_hook:)
     * The shutdown request is sent from the client to the server. It asks the server to shut down,
     * but to not exit (otherwise the response might not be delivered correctly to the client).
     * There is a separate exit notification that asks the server to exit. Clients must not send any
     * notifications other than exit or requests to a server to which they have sent a shutdown
     * request. Clients should also wait with sending the exit notification until they have received
     * a response from the shutdown request.
     * <p>
     * If a server receives requests after a shutdown request those requests should error with
     * InvalidRequest.
     * <p>
     * Request:
     * <p>
     * method: ‘shutdown’
     * params: none
     * Response:
     * <p>
     * result: null
     * error: code and message set in case an exception happens during shutdown request.
     */
    @JsonRequest
    CompletableFuture<Boolean> shutdown();

    /**
     * Exit Notification (:arrow_right:)
     * A notification to ask the server to exit its process. The server should exit with success
     * code 0 if the shutdown request has been received before; otherwise with error code 1.
     * <p>
     * Notification:
     * <p>
     * method: ‘exit’
     * params: none
     */
    @JsonNotification
    void exit();


    interface SetTraceParams {
        /**
         * The new value that should be assigned to the trace setting.
         */
        TraceValue value = null;
    }

    /**
     * SetTrace Notification
     * A notification that should be used by the client to modify the trace setting of the server.
     */
    @JsonNotification
    void setTrace(SetTraceParams params);
}
