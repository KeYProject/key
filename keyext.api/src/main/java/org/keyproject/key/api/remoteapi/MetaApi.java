/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.data.ProofMacroDesc;
import org.keyproject.key.api.data.ProofScriptCommandDesc;

/**
 * The meta segments provides functionalities around the KeY systems and environment.
 */
@JsonSegment("meta")
public interface MetaApi {
    /**
     * The current version string.
     *
     * @return version of KeY
     */
    @JsonRequest("version")
    CompletableFuture<String> getVersion();

    /**
     * @return a list of available proof macros
     */
    @JsonRequest("available_macros")
    CompletableFuture<List<ProofMacroDesc>> getAvailableMacros();

    /**
     * @return a list of available proof script commands
     */
    @JsonRequest("available_script_commands")
    CompletableFuture<List<ProofScriptCommandDesc>> getAvailableScriptCommands();
}
