package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.util.List;
import java.util.concurrent.CompletableFuture;

@JsonSegment("meta")
public interface MetaApi {
    @JsonRequest("version")
    CompletableFuture<String> getVersion();

    @JsonRequest("available_macros")
    CompletableFuture<List<ProofMacro>> getAvailableMacros();

    @JsonRequest("available_script_commands")
    CompletableFuture<List<ProofScriptCommand<?>>> getAvailableScriptCommands();
}
