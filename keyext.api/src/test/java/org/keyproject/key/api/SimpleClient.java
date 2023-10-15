package org.keyproject.key.api;

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
}
