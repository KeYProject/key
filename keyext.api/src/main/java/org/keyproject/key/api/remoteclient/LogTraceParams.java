/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

import org.eclipse.lsp4j.jsonrpc.validation.NonNull;

public record LogTraceParams(
        /**
         * The message to be logged.
         */
        @NonNull String messag,

        /**
         * Additional information that can be computed if the `trace` configuration
         * is set to `'verbose'`
         */
        String verbose) {

}
