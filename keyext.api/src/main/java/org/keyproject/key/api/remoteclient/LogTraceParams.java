package org.keyproject.key.api.remoteclient;

import org.eclipse.lsp4j.jsonrpc.validation.NonNull;

public record LogTraceParams(
        /**
         * The message to be logged.
         */
        @NonNull
        String messag,

        /**
         * Additional information that can be computed if the `trace` configuration
         * is set to `'verbose'`
         */
        String verbose
) {

}