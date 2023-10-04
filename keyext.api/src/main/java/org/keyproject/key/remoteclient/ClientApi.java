package org.keyproject.key.remoteclient;

import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.eclipse.lsp4j.jsonrpc.validation.NonNull;

import javax.annotation.Nullable;

@JsonSegment
public interface ClientApi {
    @JsonNotification
    void sayHello(String e);

    /**
     * LogTrace Notification (:arrow_left:)
     * A notification to log the trace of the server’s execution. The amount and content of these notifications depends on the current trace configuration. If trace is 'off', the server should not send any logTrace notification. If trace is 'messages', the server should not add the 'verbose' field in the LogTraceParams.
     * <p>
     * $/logTrace should be used for systematic trace reporting. For single debugging messages, the server should send window/logMessage notifications.
     * <p>
     * Notification:
     * <p>
     * method: ‘$/logTrace’
     * params: LogTraceParams defined as follows:
     */
    @JsonNotification
    void logTrace(LogTraceParams params);

    interface LogTraceParams {
        /**
         * The message to be logged.
         */
        @NonNull
        String message = null;
        /**
         * Additional information that can be computed if the `trace` configuration
         * is set to `'verbose'`
         */
        String verbose = null;
    }

    //region Window

    /**
     * ShowMessage Notification (:arrow_left:)
     * The show message notification is sent from a server to a client to ask the client to display a particular message in the user interface.
     * <p>
     * Notification:
     * <p>
     * method: ‘window/showMessage’
     * params: ShowMessageParams defined as follows:
     */
    @JsonNotification
    public void ShowMessage(ShowMessageParams params);

    interface ShowMessageParams {
        /**
         * The message type. See {@link MessageType}.
         */
        MessageType type = null;

        /**
         * The actual message.
         */
        String message = null;
    }

    enum MessageType {

        Unused,
        /**
         * An error message.
         */
        Error,
        /**
         * A warning message.
         */
        Warning,
        /**
         * An information message.
         */
        Info,
        /**
         * A log message.
         */
        Log,
        /**
         * A debug message.
         *
         * @proposed
         * @since 3.18.0
         */
        Debug
    }

    /**
     * ShowMessage Request (:arrow_right_hook:)
     * The show message request is sent from a server to a client to ask the client to display a particular message in the user interface. In addition to the show message notification the request allows to pass actions and to wait for an answer from the client.
     */
    @JsonRequest
    @Nullable
    MessageActionItem ShowMessage(ShowMessageRequestParams params);

    interface ShowMessageRequestParams {
        /**
         * The message type. See {@link MessageType}
         */
        MessageType type = null;

        /**
         * The actual message
         */
        String message = null;

        /**
         * The message action items to present.
         */
        MessageActionItem[] actions = new MessageActionItem[0];
    }

    interface MessageActionItem {
        /**
         * A short title like 'Retry', 'Open Log' etc.
         */
        String title = null;
    }

    /**
     * Show Document Request (:arrow_right_hook:)
     * New in version 3.16.0
     * <p>
     * The show document request is sent from a server to a client to ask the client to display a particular resource referenced by a URI in the user interface.
     * <p>
     * property path (optional): window.showDocument
     * property type: ShowDocumentClientCapabilities defined as follows:
     */
    @JsonRequest
    ShowDocumentResult showDocument(ShowDocumentParams params);

    interface ShowDocumentParams {
        /**
         * The uri to show.
         */
        String uri;

        /**
         * Indicates to show the resource in an external program.
         * To show, for example, `https://code.visualstudio.com/`
         * in the default WEB browser set `external` to `true`.
         */
        Boolean external;

        /**
         * An optional property to indicate whether the editor
         * showing the document should take focus or not.
         * Clients might ignore this property if an external
         * program is started.
         */
        Boolean takeFocus;

        /**
         * An optional selection range if the document is a text
         * document. Clients might ignore the property if an
         * external program is started or the file is not a text
         * file.
         */
        Range selection;
    }

    defined

    interface ShowDocumentResult {
        /**
         * A boolean indicating if the show was successful.
         */
        boolean success;
    }

    /**
     * LogMessage Notification(:arrow_left:)
     * <p>
     * The log    message notification    is sent    from the    server to    the client    to ask    the client    to log
     * a particular     message.
     */
    interface LogMessageParams {
        /**
         * The message type. See {@link MessageType}
         */
        MessageType type;

        /**
         * The actual message
         */
        String message;
    }

    /**
    Create Work

    Done Progress(:arrow_right_hook:)

    The window/workDoneProgress/    create request    is sent    from the    server to    the client    to ask
    the clie nt     to create    a work    done progress.
    */

    interface WorkDoneProgressCreateParams {
        /**
         * The token to be used to report progress.
         */
        ProgressToken token;
    }

    @JsonNotification workDoneProgressCancel();
    WorkDoneProgressCancelParams defined
    interface WorkDoneProgressCancelParams {
        /**
         * The token to be used to report progress.
         */
        ProgressToken token;
    }


    //endregion
}
