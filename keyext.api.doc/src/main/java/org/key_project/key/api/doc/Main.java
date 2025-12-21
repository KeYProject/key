/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.concurrent.Callable;
import java.util.function.Function;
import java.util.function.Supplier;

import org.key_project.key.api.doc.Metamodel.Endpoint;
import org.key_project.key.api.doc.Metamodel.Type;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import com.google.gson.JsonSerializer;
import org.jspecify.annotations.Nullable;
import picocli.CommandLine;

/**
 * @author Alexander Weigl
 * @version 1 (7/8/25)
 */
@CommandLine.Command(name = "gendoc",
    mixinStandardHelpOptions = true,
    version = "gendoc 1.0",
    description = "Generates the documentation for key.api")
public class Main implements Callable<Integer> {
    @CommandLine.Option(names = { "-s", "--source" },
        description = "Source folder for getting JavaDoc")
    private @Nullable Path source = Paths.get("keyext.api", "src", "main", "java");

    @CommandLine.Option(names = { "-o", "--output" }, description = "Output folder")
    private Path output = Paths.get("out");

    public static void main(String[] args) {
        int exitCode = new CommandLine(new Main()).execute(args);
        System.exit(exitCode);
    }

    @Override
    public Integer call() throws IOException {
        var metadata = new ExtractMetaData();
        metadata.run();
        Files.createDirectories(output);

        runGenerator(metadata.getApi(), "api.meta.json", (a) -> () -> getGson().toJson(a));
        runGenerator(metadata.getApi(), "api.meta.html", DocGen::new);
        runGenerator(metadata.getApi(), "keydata.py", PythonGenerator.PyDataGen::new);
        runGenerator(metadata.getApi(), "server.py", PythonGenerator.PyApiGen::new);
        return 0;
    }


    private void runGenerator(Metamodel.KeyApi keyApi, String target,
            Function<Metamodel.KeyApi, Supplier<String>> api) {
        try {
            var n = api.apply(keyApi);
            Files.writeString(output.resolve(target), n.get());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static Gson getGson() {
        return new GsonBuilder()
                .setPrettyPrinting()
                .registerTypeAdapter(Type.class,
                    (JsonSerializer<Type>) (src, typeOfSrc, context) -> {
                        JsonObject json = (JsonObject) context.serialize(src);
                        json.addProperty("kind", src.kind());
                        return json;
                    })
                .registerTypeAdapter(Endpoint.class,
                    (JsonSerializer<Endpoint>) (src, typeOfSrc, context) -> {
                        JsonObject json = (JsonObject) context.serialize(src);
                        json.addProperty("kind", src.kind());
                        return json;
                    })
                .create();
    }
}
