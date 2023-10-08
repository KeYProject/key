/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.json.StreamMessageProducer;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteclient.ClientApi;

public class Client {
    public static void main(String[] args)
            throws IOException, ExecutionException, InterruptedException, TimeoutException {
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

        var clientListening = clientLauncher.startListening();
        var serverListening = serverLauncher.startListening();

        // clientLauncher.getRemoteProxy().examples();
        serverLauncher.getRemoteProxy().sayHello("Alex");

        serverListening.get(1, TimeUnit.SECONDS);
        clientListening.get(1, TimeUnit.SECONDS);
    }
}
