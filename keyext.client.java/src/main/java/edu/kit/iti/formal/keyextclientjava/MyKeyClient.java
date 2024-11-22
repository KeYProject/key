/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.keyextclientjava;

import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import java.util.logging.Logger;
import javafx.geometry.Orientation;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;

import edu.kit.iti.formal.keyextclientjava.rpc.KeyRemote;
import edu.kit.iti.formal.keyextclientjava.rpc.RPCLayer;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.json.StreamMessageProducer;
import org.keyproject.key.api.KeyApiImpl;
import org.keyproject.key.api.StartServer;
import org.keyproject.key.api.data.KeyIdentifications;
import org.keyproject.key.api.data.LoadParams;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteapi.PrintOptions;
import org.keyproject.key.api.remoteclient.*;
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular;
import org.kordamp.ikonli.javafx.FontIcon;

public class MyKeyClient {
    public static final String JAR_FILE = "";
    private final ToolBar toolbar = new ToolBar();
    private final Label txtStatus = new Label("Yeah!");
    public final BorderPane root = new BorderPane();
    private final TreeView<Object> tnid = new TreeView<>();
    private final TextArea txtSequentView = new TextArea();

    private final FileChooser fc = new FileChooser();
    private final KeyApi keyApi;
    private KeyIdentifications.ProofId loadedProof;

    public MyKeyClient() throws IOException {
        // region toolbar
        var btnOpen = new Button("Open", new FontIcon(FontAwesomeRegular.FOLDER_OPEN));
        btnOpen.setOnAction(actionEvent -> openFile());
        toolbar.getItems().setAll(btnOpen, new Separator(Orientation.VERTICAL));
        // endregion

        var splitCenter = new SplitPane(tnid, txtSequentView);
        splitCenter.setDividerPositions(.2);
        root.setTop(toolbar);
        root.setCenter(splitCenter);
        root.setBottom(txtStatus);

        // var startKey = ForkJoinPool.commonPool().submit(this::startKey);

        PipedInputStream inClient = new PipedInputStream();
        PipedOutputStream outClient = new PipedOutputStream();
        PipedInputStream inServer = new PipedInputStream();
        PipedOutputStream outServer = new PipedOutputStream();

        inClient.connect(outServer);
        outClient.connect(inServer);

        KeyApiImpl impl = new KeyApiImpl();
        Launcher<ClientApi> serverLauncher = StartServer.launch(outServer, inServer, impl);
        impl.setClientApi(serverLauncher.getRemoteProxy());

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

        clientLauncher.startListening();
        serverLauncher.startListening();

        this.keyApi = clientLauncher.getRemoteProxy();
    }

    private Object startKey() throws IOException {
        return new KeyRemote(RPCLayer.startWithCLI(JAR_FILE));
    }

    private void openFile() {
        var sel = fc.showOpenDialog(null);
        if (sel != null) {
            try {
                loadedProof = keyApi.load(
                    new LoadParams(sel, null, null, null, null))
                        .get().getRight();
                var root = keyApi.root(loadedProof).get();
                var sequent =
                    keyApi.print(root.nodeid(), new PrintOptions(true, 80, 4, true, false))
                            .get();
                txtSequentView.setText(sequent.result());
            } catch (ProblemLoaderException e) {
                throw new RuntimeException(e);
            } catch (ExecutionException e) {
                throw new RuntimeException(e);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }


        }
    }

    private class SimpleClient implements ClientApi {
        @Override
        public void sayHello(String e) {

        }

        @Override
        public void logTrace(LogTraceParams params) {

        }

        @Override
        public void showMessage(ShowMessageParams params) {

        }

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

        }

        @Override
        public void taskProgress(int position) {

        }

        @Override
        public void taskStarted(TaskStartedInfo info) {

        }
    }
}
