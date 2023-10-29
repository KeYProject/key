package org.keyproject.key.api.remoteapi;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.ProofMacroDesc;
import org.keyproject.key.api.data.ProofScriptCommandDesc;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import org.keyproject.key.api.data.KeyIdentifications.*;

@JsonSegment("meta")
public interface MetaApi {
    @JsonRequest("version")
    CompletableFuture<String> getVersion();

    @JsonRequest("available_macros")
    CompletableFuture<List<ProofMacroDesc>> getAvailableMacros();

    @JsonRequest("available_script_commands")
    CompletableFuture<List<ProofScriptCommandDesc>> getAvailableScriptCommands();
}
