package org.keyproject.key.api;


import com.google.gson.GsonBuilder;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.websocket.jakarta.WebSocketLauncherBuilder;
import org.keyproject.key.api.adapters.KeyAdapter;
import org.keyproject.key.api.remoteclient.ClientApi;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.Option;

import javax.annotation.Nullable;
import java.io.*;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.ExecutionException;

/**
 * @author Alexander Weigl
 * @version 1 (07.10.23)
 */
@CommandLine.Command
public class StartServer implements Runnable {
    private static final Logger LOGGER = LoggerFactory.getLogger(StartServer.class);

    //region CLI arguments
    @Option(names = "--std", description = "use stdout and stdin for communication")
    boolean stdStreams;
    @Option(names = "--trace", description = "use stdout and stdin for communication")
    boolean enableTracing;

    @Option(names = "--server", paramLabel = "PORT", description = "enables the TCP server mode")
    @Nullable
    Integer serverPort;

    @Option(names = "--connectTo", paramLabel = "PORT", description = "enables the TCP client mode")
    @Nullable
    Integer clientPort;


    @Option(names = "--infile", paramLabel = "FILE or PIPE", description = "read from named pipe or file")
    @Nullable
    File inFile;

    @Option(names = "--outfile", paramLabel = "FILE or PIPE", description = "write to named pipe or file")
    File outFile;

    @Option(names = {"-h", "--help"}, usageHelp = true, description = "display a help message")
    boolean helpRequested = false;

    @Option(names = "--websocket")
    boolean websocket = false;
    //endregion

    public static void main(String[] args) {
        new CommandLine(new StartServer()).execute(args);
    }

    private InputStream in;
    private OutputStream out;

    private void establishStreams() throws IOException {
        in = System.in;
        out = System.out;

        if (stdStreams) {
            return;
        }

        if (clientPort != null) {
            var socket = new Socket(InetAddress.getLocalHost(), clientPort);
            socket.setKeepAlive(true);
            socket.setTcpNoDelay(true);
            in = socket.getInputStream();
            out = socket.getOutputStream();
            return;
        }

        if (serverPort != null) {
            var server = new ServerSocket(serverPort);
            LOGGER.info("Waiting on port {}", serverPort);
            var socket = server.accept();
            LOGGER.info("Connection to client established: {}", socket.getRemoteSocketAddress());
            socket.setKeepAlive(true);
            socket.setTcpNoDelay(true);
            in = socket.getInputStream();
            out = socket.getOutputStream();
            return;
        }


        if (inFile != null) {
            in = new FileInputStream(inFile);
        }

        if (outFile != null) {
            out = new FileOutputStream(outFile);
        }

        if (out == null || in == null) {
            throw new IllegalStateException("Could not initialize the streams");
        }
    }


    @Override
    public void run() {
        if (helpRequested) {
            return;
        }

        try {
            final var keyApi = new KeyApiImpl();

            if (websocket) {
                var launcherBuilder = new WebSocketLauncherBuilder<ClientApi>()
                        .setOutput(out)
                        .setInput(in)
                        .traceMessages(new PrintWriter(System.err))
                        .validateMessages(true);
                launcherBuilder.configureGson(StartServer::configureJson);
                launcherBuilder.setLocalService(keyApi);
                launcherBuilder.setRemoteInterface(ClientApi.class);

                final var clientApiLauncher = launcherBuilder.create();
                keyApi.setClientApi(clientApiLauncher.getRemoteProxy());
                clientApiLauncher.startListening().get();
            } else {
                establishStreams();
                try (var lin = in; var lout = out) {
                    var listener = launch(lout, lin, keyApi);
                    LOGGER.info("JSON-RPC is listening for requests");
                    keyApi.setClientApi(listener.getRemoteProxy());
                    listener.startListening().get();
                }
            }
        } catch (IOException | InterruptedException | ExecutionException e) {
            throw new RuntimeException(e);
        }
    }


    public static void configureJson(GsonBuilder gsonBuilder) {
        gsonBuilder.registerTypeHierarchyAdapter(Object.class, new GenericSerializer());
        gsonBuilder.registerTypeAdapter(File.class, new KeyAdapter.FileTypeAdapter());
        gsonBuilder.registerTypeAdapter(Throwable.class, new KeyAdapter.ThrowableAdapter());
    }

    public static Launcher<ClientApi> launch(OutputStream out, InputStream in, KeyApiImpl keyApi) {
        // var localServices = getLocalServices();
        // var remoteInterfaces = getRemoteInterfaces();
        var launcherBuilder = new Launcher.Builder<ClientApi>()
                .setOutput(out)
                .setInput(in)
                .traceMessages(new PrintWriter(System.err))
                .validateMessages(true);

        launcherBuilder.configureGson(StartServer::configureJson);
        //if (localServices != null && !localServices.isEmpty())
        launcherBuilder.setLocalService(keyApi);
        //if (remoteInterfaces != null && !remoteInterfaces.isEmpty())
        launcherBuilder.setRemoteInterface(ClientApi.class);

        return launcherBuilder.create();
    }
}

