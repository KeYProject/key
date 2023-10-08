package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.util.List;
import java.util.concurrent.CompletableFuture;

@JsonSegment("meta")
public interface KeyMetaApi {
    @JsonRequest
    CompletableFuture<String> getVersion();

    @JsonRequest
    CompletableFuture<List<MacroDescription>> getAvailableMacros();

    @JsonRequest
    CompletableFuture<List<ProofScriptCommand<?>>> getAvailableScriptCommands();
}
