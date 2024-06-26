/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uka.ilkd.key.proof.Proof;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.google.gson.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteclient.ClientApi;
import sun.misc.Unsafe;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
public class ExtractMetaData {
    private static PrintWriter out;

    private static final List<Metamodel.Endpoint> endpoints = new LinkedList<>();
    private static final List<Metamodel.Type> types = new LinkedList<>();
    private static final Metamodel.KeyApi keyApi = new Metamodel.KeyApi(endpoints, types);

    public static void main(String[] args) {
        for (Method method : KeyApi.class.getMethods()) {
            addServerEndpoint(method);
        }

        for (Method method : ClientApi.class.getMethods()) {
            addClientEndpoint(method);
        }

        runGenerator("api.meta.json", (a) -> () -> getGson().toJson(a));
        runGenerator("api.meta.md", DocGen::new);
        runGenerator("keydata.py", PythionGenerator.PyDataGen::new);
        runGenerator("server.py", PythionGenerator.PyApiGen::new);
    }

    private static void runGenerator(String target,
            Function<Metamodel.KeyApi, Supplier<String>> api) {
        try {
            var n = api.apply(keyApi);
            Files.writeString(Paths.get(target), n.get());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static Gson getGson() {
        return new GsonBuilder()
                .setPrettyPrinting()
                .registerTypeAdapter(Type.class, new JsonSerializer<Metamodel.Type>() {
                    @Override
                    public JsonElement serialize(Metamodel.Type src, Type typeOfSrc,
                            JsonSerializationContext context) {
                        JsonObject json = (JsonObject) context.serialize(src);
                        json.addProperty("kind", src.kind());
                        return json;
                    }
                })
                .create();
    }

    private static void addServerEndpoint(Method method) {
        var jsonSegment = method.getDeclaringClass().getAnnotation(JsonSegment.class);
        if (jsonSegment == null)
            return;
        var segment = jsonSegment.value();

        var req = method.getAnnotation(JsonRequest.class);
        var resp = method.getAnnotation(JsonNotification.class);

        var args = translate(method.getParameters());

        if (req != null) {
            var mn = callMethodName(method.getName(), segment, req.value(), req.useSegment());

            if (method.getReturnType() == Void.class) {
                System.err.println("Found void as return type for a request!  " + method);
                return;
            }

            var retType = getOrFindType(method.getGenericReturnType());
            Objects.requireNonNull(retType, "No retType found " + method.getGenericReturnType());
            var documentation = findDocumentation(method);
            var mm = new Metamodel.ServerRequest(mn, documentation, args, retType);
            endpoints.add(mm);
            return;
        }

        if (resp != null) {
            var mn = callMethodName(method.getName(), segment, resp.value(), resp.useSegment());
            var documentation = findDocumentation(method);
            var mm = new Metamodel.ServerNotification(mn, documentation, args);
            endpoints.add(mm);
            return;
        }

        throw new IllegalStateException();
    }

    private static String findDocumentation(Method method) {
        // TODO get compilation, get type, find method, getJavaDocComment()
        return "";
    }

    private static List<Metamodel.Argument> translate(Parameter[] parameters) {
        return Arrays.stream(parameters).map(ExtractMetaData::translate).toList();
    }

    private static Metamodel.Argument translate(Parameter parameter) {
        var type = getOrFindType(parameter.getType()).name();
        return new Metamodel.Argument(parameter.getName(), type);
    }

    private static Metamodel.Type getOrFindType(Class<?> type) {
        System.out.println(type);
        if (type == CompletableFuture.class) {
            return getOrFindType(type.getTypeParameters()[0].getClass());
        }

        if (type == Unsafe.class || type == Class.class || type == Constructor.class
                || type == Proof.class) {
            throw new IllegalStateException("Forbidden class reached!");
        }

        if (type == String.class)
            return Metamodel.BuiltinType.STRING;
        if (type == Integer.class)
            return Metamodel.BuiltinType.INT;
        if (type == Double.class)
            return Metamodel.BuiltinType.DOUBLE;
        if (type == Long.class)
            return Metamodel.BuiltinType.LONG;
        if (type == Character.class)
            return Metamodel.BuiltinType.LONG;
        if (type == File.class)
            return Metamodel.BuiltinType.STRING;
        if (type == Boolean.class)
            return Metamodel.BuiltinType.BOOL;
        if (type == Boolean.TYPE)
            return Metamodel.BuiltinType.BOOL;

        if (type == Integer.TYPE)
            return Metamodel.BuiltinType.INT;
        if (type == Double.TYPE)
            return Metamodel.BuiltinType.DOUBLE;
        if (type == Long.TYPE)
            return Metamodel.BuiltinType.LONG;
        if (type == Character.TYPE)
            return Metamodel.BuiltinType.LONG;

        System.out.println(type);
        var t = types.stream().filter(it -> it.name().equals(type.getSimpleName())).findFirst();
        if (t.isPresent())
            return t.get();
        var a = createType(type);
        types.add(a);
        return a;
    }

    private static Metamodel.Type createType(Class<?> type) {
        final var documentation = findDocumentation(type);
        if (type.isEnum())
            return new Metamodel.EnumType(type.getSimpleName(),
                Arrays.stream(type.getEnumConstants()).map(Object::toString).toList(),
                documentation);


        var obj = new Metamodel.ObjectType(type.getSimpleName(), new ArrayList<>(), documentation);
        final var list = Arrays.stream(type.getDeclaredFields())
                .map(it -> new Metamodel.Field(it.getName(), getOrFindType(it.getType()).name()))
                .toList();
        obj.fields().addAll(list);
        return obj;
    }

    private static String findDocumentation(Class<?> type) {
        var parser = initJavaParser();
        var fileName = findFileForType(type);

        if (Files.exists(fileName)) {
            try {
                return parser.parse(fileName).getResult().flatMap(CompilationUnit::getPrimaryType)
                        .flatMap(NodeWithJavadoc::getJavadocComment)
                        .map(Comment::getContent).orElse("");
            } catch (IOException e) {
                e.printStackTrace();
                return "";
            }
        } else
            return "";
    }

    private static Path findFileForType(Class<?> type) {
        final var folderString = type.getPackageName().replaceAll("\\.", "/");
        var folder = Paths.get("keyext.api", "src", "main", "java", folderString);
        final Class<?> declaringClass = type.getDeclaringClass();
        var fileName = (declaringClass != null ? declaringClass : type).getSimpleName() + ".java";
        var file = folder.resolve(fileName);
        return file;
    }


    private static void addClientEndpoint(Method method) {
        var jsonSegment = method.getDeclaringClass().getAnnotation(JsonSegment.class);
        var segment = jsonSegment.value();

        var req = method.getAnnotation(JsonRequest.class);
        var resp = method.getAnnotation(JsonNotification.class);

        var args = translate(method.getParameters());

        if (req != null) {
            var retType = getOrFindType(method.getGenericReturnType());
            Objects.requireNonNull(retType);
            var mn = callMethodName(method.getName(), segment, req.value(), req.useSegment());
            var documentation = findDocumentation(method);
            var mm = new Metamodel.ClientRequest(mn, documentation, args, retType);
            endpoints.add(mm);
            return;
        }

        if (resp != null) {
            var mn = callMethodName(method.getName(), segment, resp.value(), resp.useSegment());
            var documentation = findDocumentation(method);
            var mm = new Metamodel.ClientNotification(mn, documentation, args);
            endpoints.add(mm);
        }
    }

    private static String callMethodName(String method, String segment, String userValue,
            boolean useSegment) {
        if (!useSegment) {
            if (userValue == null || userValue.isBlank()) {
                return method;
            } else {
                return userValue;
            }
        } else {
            if (userValue == null || userValue.isBlank()) {
                return segment + "/" + method;
            } else {
                return segment + "/" + userValue;
            }
        }
    }

    private static Metamodel.Type getOrFindType(Type genericReturnType) {
        if (genericReturnType instanceof Class c)
            return getOrFindType(c);
        if (genericReturnType instanceof ParameterizedType pt) {
            if (Objects.equals(pt.getRawType().getTypeName(),
                CompletableFuture.class.getTypeName())) {
                return getOrFindType(pt.getActualTypeArguments()[0]);
            }
            if (Objects.equals(pt.getRawType().getTypeName(), List.class.getTypeName())) {
                var base = getOrFindType(pt.getActualTypeArguments()[0]);
                return new Metamodel.ListType(base, "");
            }

            if (Objects.equals(pt.getRawType().getTypeName(), Either.class.getTypeName())) {
                var base1 = getOrFindType(pt.getActualTypeArguments()[0]);
                var base2 = getOrFindType(pt.getActualTypeArguments()[1]);
                return new Metamodel.EitherType(base1, base2, "");
            }
        }
        return null;
    }

    static JavaParser initJavaParser() {
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17_PREVIEW);
        config.setAttributeComments(true);
        config.setLexicalPreservationEnabled(false);
        config.setStoreTokens(false);
        config.setIgnoreAnnotationsWhenAttributingComments(true);
        config.setDoNotAssignCommentsPrecedingEmptyLines(true);
        return new JavaParser(config);
    }

}
