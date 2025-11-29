/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

import java.util.concurrent.CompletableFuture;
import javax.annotation.Nullable;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.jspecify.annotations.NullMarked;
import org.keyproject.key.api.data.TaskFinishedInfo;
import org.keyproject.key.api.data.TaskStartedInfo;

/**
 * This segment contains the functionalities that a client needs to implement.
 * Mainly, it is logging and displaying of information.
 */
@JsonSegment("client")
@NullMarked
public interface ClientApi {
    /**
     * A notification to log the trace of the server’s execution.
     * The amount and content of these notifications depends on the current trace configuration.
     * If trace is 'off', the server should not send any logTrace notification.
     * If trace is 'messages', the server should not add the 'verbose' field in the LogTraceParams.
     * <p>
     * $/logTrace should be used for systematic trace reporting. For single debugging messages, the
     * server should send window/logMessage notifications.
     */
    @JsonNotification
    void logTrace(LogTraceParams params);

    // region Window

    /**
     * The show message notification is sent from a server to a client to ask the client to display
     * a particular message in the user interface.
     */
    @JsonNotification("showMessage")
    void showMessage(ShowMessageParams params);

    /**
     * The show message request is sent from a server to a client to ask the client to display a
     * particular message in the user interface. In addition to the show message notification the
     * request allows to pass actions and to wait for an answer from the client.
     */
    @JsonRequest
    @Nullable
    CompletableFuture<MessageActionItem> showMessageWithActions(ShowMessageRequestParams params);


    /**
     * The show document request is sent from a server to a client to ask the client to display a
     * particular resource referenced by a URI in the user interface.
     */
    @JsonRequest
    CompletableFuture<ShowDocumentResult> showDocument(ShowDocumentParams params);


    /**
     * Notifiation about the finishing of a task.
     *
     * @param info task information
     */
    @JsonNotification
    void taskFinished(TaskFinishedInfo info);

    /**
     * Progress on the current task running
     *
     * @param position some integer
     * @TODO weigl: This call is stupid w/o information of the task assigned.
     *       we also should send max value for showing a progress indicator,
     *       and a message.
     */
    @JsonNotification
    void taskProgress(int position);

    /**
     * This call notifies the client that a task has been started.
     * Task are started, mainly triggered by the client, for various reason, e.g.,
     * letting the macro run.
     *
     * @param info information about the task
     */
    @JsonNotification
    void taskStarted(TaskStartedInfo info);
    // endregion
}
