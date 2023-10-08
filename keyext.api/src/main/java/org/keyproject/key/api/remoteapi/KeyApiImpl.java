package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.gui.Example;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.util.KeYConstants;
import org.eclipse.lsp4j.jsonrpc.CompletableFutures;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

import java.util.List;
import java.util.concurrent.CompletableFuture;

@JsonSegment
public class KeyApiImpl implements KeyApi {
    @Override
    @JsonRequest
    public CompletableFuture<List<Example>> examples() {
        return CompletableFutures.computeAsync((c) -> ExampleChooser.listExamples(ExampleChooser.lookForExamples()));
    }

    @Override
    public CompletableFuture<Void> shutdown() {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {

    }

    @Override
    public void setTrace(SetTraceParams params) {

    }

    @Override
    public CompletableFuture<String> getVersion() {
        return CompletableFuture.completedFuture(KeYConstants.VERSION);
    }

    @Override
    public CompletableFuture<List<MacroDescription>> getAvailableMacros() {
        return CompletableFuture.completedFuture(
                KeYApi.getMacroApi().getMacros().stream().map(MacroDescription::from)
                        .toList()
        );
    }

    @Override
    public CompletableFuture<List<ProofScriptCommand<?>>> getAvailableScriptCommands() {
        return CompletableFuture.completedFuture(
                KeYApi.getScriptCommandApi().getScriptCommands().stream().toList());
    }
}
