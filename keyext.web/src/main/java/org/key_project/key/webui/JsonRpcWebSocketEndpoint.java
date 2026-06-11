package org.key_project.key.webui;

import jakarta.websocket.OnClose;
import jakarta.websocket.OnError;
import jakarta.websocket.OnOpen;
import jakarta.websocket.Session;
import jakarta.websocket.server.ServerEndpoint;
import org.eclipse.lsp4j.websocket.jakarta.WebSocketLauncherBuilder;
import org.keyproject.key.api.KeyApiImpl;
import org.keyproject.key.api.StartServer;
import org.keyproject.key.api.remoteclient.ClientApi;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.06.26)
 */
@ServerEndpoint("/ws/jsonrpc")
public class JsonRpcWebSocketEndpoint {
    private static final ExecutorService threadPool = Executors.newCachedThreadPool();
    private static final KeyApiImpl keyApi = new KeyApiImpl();

    @OnOpen
    public void onOpen(Session session) throws IOException, ExecutionException, InterruptedException {

        var launcherBuilder = new WebSocketLauncherBuilder<ClientApi>()
                .setSession(session)
                .traceMessages(new PrintWriter(System.err))
                .validateMessages(true);

        launcherBuilder.configureGson(StartServer::configureJson);
        launcherBuilder.setLocalService(keyApi);
        launcherBuilder.setRemoteInterface(ClientApi.class);

        var launcher = launcherBuilder.create();
        final var clientApiLauncher = launcherBuilder.create();
        keyApi.setClientApi(clientApiLauncher.getRemoteProxy());
        clientApiLauncher.startListening().get();
    }

    @OnClose
    public void onClose(Session session) {
        // Connection closed - cleanup handled by launcher
    }

    @OnError
    public void onError(Session session, Throwable throwable) {
        throwable.printStackTrace();
    }
}
