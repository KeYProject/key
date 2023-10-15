package org.keyproject.key.api;

import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.json.StreamMessageProducer;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteclient.ClientApi;

import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;

public class TestRpc {
    private Future<Void> clientListening, serverListening;
    private KeyApi keyApi;

    @BeforeEach
    void setup() throws IOException, ExecutionException, InterruptedException, TimeoutException {
        PipedInputStream inClient = new PipedInputStream();
        PipedOutputStream outClient = new PipedOutputStream();
        PipedInputStream inServer = new PipedInputStream();
        PipedOutputStream outServer = new PipedOutputStream();

        inClient.connect(outServer);
        outClient.connect(inServer);

        Launcher<ClientApi> serverLauncher = StartServer.launch(outServer, inServer);

        var client = new SimpleClient();
        Launcher<KeyApi> clientLauncher = new Launcher.Builder<KeyApi>()
                .setLocalService(client)
                .setRemoteInterfaces(Collections.singleton(KeyApi.class))
                .setInput(inClient)
                .setOutput(outClient)
                .configureGson(StartServer::configureJson)
                .traceMessages(new PrintWriter(System.err))
                .create();

        Logger logger = Logger.getLogger(StreamMessageProducer.class.getName());
        logger.setLevel(Level.SEVERE);

        clientListening = clientLauncher.startListening();
        serverListening = serverLauncher.startListening();

        keyApi = clientLauncher.getRemoteProxy();
    }

    @AfterEach
    void teardown() throws ExecutionException, InterruptedException, TimeoutException {
        serverListening.cancel(true);
        clientListening.cancel(true);
    }


    @Test
    public void hello() {

    }

    @Test
    public void listMacros() throws ExecutionException, InterruptedException {
        var examples = keyApi.getAvailableMacros().get();
        System.out.println(examples);
    }

    @Test
    public void listExamples() throws ExecutionException, InterruptedException {
        var examples = keyApi.examples().get();
        System.out.println(examples);
    }
}
