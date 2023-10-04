package org.keyproject.key.remoteapi;

import com.google.gson.GsonBuilder;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.keyproject.key.FileTypeAdapter;
import org.keyproject.key.remoteclient.ClientApi;

import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;

public class Main {
    public static void main(String[] args) throws ExecutionException, InterruptedException {
        var future = launch(System.out, System.in);
        future.startListening();
    }

    public static Launcher<ClientApi> launch(OutputStream out, InputStream in) {
        var localServices = getLocalServices();
        var remoteInterfaces = getRemoteInterfaces();
        var launcherBuilder = new Launcher.Builder<ClientApi>()
                .setOutput(out)
                .setInput(in)
                .traceMessages(new PrintWriter(System.err))
                .validateMessages(true);

        launcherBuilder.configureGson(Main::configureJson);

        //if (localServices != null && !localServices.isEmpty())
        launcherBuilder.setLocalService(new KeyApiImpl());
        //if (remoteInterfaces != null && !remoteInterfaces.isEmpty())
        launcherBuilder.setRemoteInterface(ClientApi.class);

        var launcher = launcherBuilder.create();
        return launcher;
    }

    public static void configureJson(GsonBuilder gsonBuilder) {
        gsonBuilder.registerTypeAdapter(File.class, new FileTypeAdapter());
    }

    private static Collection<Class<? extends ClientApi>> getRemoteInterfaces() {
        return Collections.singleton(ClientApi.class);
      /*  return ServiceLoader.load(ClientService.class)
                .stream()
                .map(ServiceLoader.Provider::type)
                .collect(Collectors.toSet());
       */
    }

    private static List<Object> getLocalServices() {
        return Collections.singletonList(new KeyApiImpl());
        /*return ServiceLoader.load(KeyService.class)
                .stream().map(ServiceLoader.Provider::get)
                .map(it -> (Object) it)
                .toList();*/
    }
}
