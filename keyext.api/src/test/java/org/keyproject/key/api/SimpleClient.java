package org.keyproject.key.api;

import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import org.keyproject.key.api.remoteclient.*;

import javax.annotation.Nullable;
import java.util.concurrent.CompletableFuture;

class SimpleClient implements ClientApi {

    @Override
    public void sayHello(String e) {
        System.out.format("Hello, %s%n", e);
    }

    @Override
    public void logTrace(LogTraceParams params) {

    }

    @Override
    public void showMessage(ShowMessageParams params) {

    }

    @Nullable
    @Override
    public CompletableFuture<MessageActionItem> userResponse(ShowMessageRequestParams params) {
        return null;
    }

    @Override
    public CompletableFuture<ShowDocumentResult> showDocument(ShowDocumentParams params) {
        return null;
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        System.out.println(info);
    }

    @Override
    public void taskProgress(int position) {

    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        System.out.println(info);
    }
}
