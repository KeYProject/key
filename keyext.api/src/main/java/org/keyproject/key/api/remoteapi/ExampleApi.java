package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.gui.Example;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.util.List;
import java.util.concurrent.CompletableFuture;

@JsonSegment("examples")
public interface ExampleApi {
    @JsonRequest("list")
    CompletableFuture<List<Example>> examples();
}
