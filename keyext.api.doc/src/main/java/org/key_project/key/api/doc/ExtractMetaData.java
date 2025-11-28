/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;/*
                                     * This file is part of KeY - https://key-project.org
                                     * KeY is licensed under the GNU General Public License Version
                                     * 2
                                     * SPDX-License-Identifier: GPL-2.0-only
                                     */

import java.io.File;
import java.lang.reflect.*;
import java.util.*;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.Proof;

import com.github.therapi.runtimejavadoc.ClassJavadoc;
import com.github.therapi.runtimejavadoc.FieldJavadoc;
import com.github.therapi.runtimejavadoc.MethodJavadoc;
import com.github.therapi.runtimejavadoc.RuntimeJavadoc;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteclient.ClientApi;
import picocli.CommandLine;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
@NullMarked
@CommandLine.Command(name = "gendoc",
    mixinStandardHelpOptions = true,
    version = "gendoc 1.0",
    description = "Generates the documentation for key.api")
public class ExtractMetaData implements Callable<Integer> {
    private final List<Metamodel.Endpoint> endpoints = new LinkedList<>();
    private final Map<Class<?>, Metamodel.Type> types = new HashMap<>();
    private final Metamodel.KeyApi keyApi = new Metamodel.KeyApi(endpoints, types);

    public ExtractMetaData() {}

    @Override
    public Integer call() throws IOException {
        if (source != null) {
            ParserConfiguration config = new ParserConfiguration();
            config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
            config.setAttributeComments(true);
            config.setLexicalPreservationEnabled(false);
            config.setStoreTokens(false);
            config.setIgnoreAnnotationsWhenAttributingComments(true);
            config.setDoNotAssignCommentsPrecedingEmptyLines(true);
            sourceRoot = new SourceRoot(source, config);
        }

        for (Method method : KeyApi.class.getMethods()) {
            addServerEndpoint(method);
        }

        for (Method method : ClientApi.class.getMethods()) {
            addClientEndpoint(method);
        }

        Files.createDirectories(output);

        runGenerator("api.meta.json", (a) -> () -> getGson().toJson(a));
        runGenerator("api.meta.md", DocGen::new);
        runGenerator("keydata.py", PythonGenerator.PyDataGen::new);
        runGenerator("server.py", PythonGenerator.PyApiGen::new);

        return 0;
    }

    private void runGenerator(String target, Function<Metamodel.KeyApi, Supplier<String>> api) {
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
                    (JsonSerializer<Metamodel.Type>) (src, typeOfSrc, context) -> {
                        JsonObject json = (JsonObject) context.serialize(src);
                        json.addProperty("kind", src.kind());
                        return json;
                    })
                .create();
    }

    private void addServerEndpoint(Method method) {
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

        throw new IllegalStateException(
            "Method " + method + " is neither a request nor a notification");
    }

    private String findDocumentation(Method method) {
        MethodJavadoc javadoc = RuntimeJavadoc.getJavadoc(method);
        return javadoc.getParams().toString() +
                javadoc.getThrows() +
                javadoc.getReturns().toString();

        /*
         * return findCompilationUnit(method.getDeclaringClass())
         * .map(it -> it.getMethodsByName(method.getName()))
         * .map(List::getFirst)
         * .flatMap(NodeWithJavadoc::getJavadoc)
         * .map(Javadoc::getDescription)
         * .map(JavadocDescription::toText)
         * .orElse("");
         */
    }

    private List<Metamodel.Argument> translate(Parameter[] parameters) {
        return Arrays.stream(parameters).map(this::translate).toList();
    }

    private Metamodel.Argument translate(Parameter parameter) {
        var type = getOrFindType(parameter.getType()).name();
        return new Metamodel.Argument(parameter.getName(), type);
    }

    private Metamodel.Type getOrFindType(Class<?> type) {
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

        if (type == CompletableFuture.class) {
            return getOrFindType(type.getTypeParameters()[0].getClass());
        }


        if (type == List.class) {
            // TODO try to get the type below.
            var subType = getOrFindType(type.getTypeParameters()[0]);
            return new Metamodel.ListType(subType, "");
        }

        if (type == Class.class || type == Constructor.class || type == Proof.class) {
            throw new IllegalStateException("Forbidden class reached!");
        }


        var t = types.get(type);
        if (t != null)
            return t;
        var a = createType(type);
        types.put(type, a);
        return a;
    }

    private Metamodel.Type createType(Class<?> type) {

        final var documentation = findDocumentation(type);
        if (type.isEnum())
            return new Metamodel.EnumType(type.getSimpleName(), type.getName(),
                Arrays.stream(type.getEnumConstants())
                        .map(
                            it -> new Metamodel.EnumConstant(it.toString(),
                                findDocumentation(type, it)))
                        .toList(),
                documentation);


        var obj = new Metamodel.ObjectType(type.getSimpleName(), type.getName(), new ArrayList<>(),
            documentation);
        final var list = Arrays.stream(type.getDeclaredFields())
                .map(it -> new Metamodel.Field(it.getName(), getOrFindTypeName(it.getGenericType()),
                    findDocumentation(it)))
                .toList();
        obj.fields().addAll(list);
        return obj;
    }

    private String findDocumentation(Field it) {
        var javadoc = RuntimeJavadoc.getJavadoc(it);
        return printFieldDocumentation(javadoc);
    }

    private @Nullable String findDocumentation(Class<?> type, Object enumConstant) {
        ClassJavadoc javadoc = RuntimeJavadoc.getJavadoc(type);
        for (var cdoc : javadoc.getEnumConstants()) {
            if (cdoc.getName().equalsIgnoreCase(enumConstant.toString())) {
                return printFieldDocumentation(cdoc);
            }
        }
        return null;
    }

    private static String printFieldDocumentation(FieldJavadoc cdoc) {
        return cdoc.getComment().toString() +
                (cdoc.getOther().isEmpty() ? "" : cdoc.getOther().toString()) +
                (cdoc.getSeeAlso().isEmpty() ? "" : cdoc.getSeeAlso().toString());
    }

    private String findDocumentation(Class<?> type) {
        ClassJavadoc classDoc = RuntimeJavadoc.getJavadoc(type);
        if (!classDoc.isEmpty()) { // optionally skip absent documentation
            return classDoc.getComment().toString() + classDoc.getOther() + classDoc.getSeeAlso();
        }
        return "";
    }

    private void addClientEndpoint(Method method) {
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

    private static String callMethodName(String method, String segment, @Nullable String userValue,
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


    private String getOrFindTypeName(Type type) {
        switch (type) {
            case GenericArrayType a -> throw new RuntimeException("Unwanted type found: " + type);
            case Class<?> c -> {
                return getOrFindTypeName(c);
            }
            case ParameterizedType pt -> {
                if (Objects.equals(pt.getRawType().getTypeName(),
                    CompletableFuture.class.getTypeName())) {
                    return getOrFindTypeName(pt.getActualTypeArguments()[0]);
                }
                if (Objects.equals(pt.getRawType().getTypeName(), List.class.getTypeName())) {
                    String base = getOrFindTypeName(pt.getActualTypeArguments()[0]);
                    return base + "[]";
                }

                if (Objects.equals(pt.getRawType().getTypeName(), Either.class.getTypeName())) {
                    var base1 = getOrFindType(pt.getActualTypeArguments()[0]);
                    var base2 = getOrFindType(pt.getActualTypeArguments()[1]);
                    return "either<" + base1 + ", " + base2 + ">";
                }
            }
            default -> {
            }
        }

        return "<error>!!!";
    }

    private String getOrFindTypeName(Class<?> type) {
        var t = types.get(type);

        if (t != null)
            return t.name();
        else if (type == String.class)
            return Metamodel.BuiltinType.STRING.name();
        else if (type == Integer.class)
            return Metamodel.BuiltinType.INT.name();
        else if (type == Double.class)
            return Metamodel.BuiltinType.DOUBLE.name();
        else if (type == Long.class)
            return Metamodel.BuiltinType.LONG.name();
        else if (type == Character.class)
            return Metamodel.BuiltinType.LONG.name();
        else if (type == File.class)
            return Metamodel.BuiltinType.STRING.name();
        else if (type == Boolean.class)
            return Metamodel.BuiltinType.BOOL.name();
        else if (type == Boolean.TYPE)
            return Metamodel.BuiltinType.BOOL.name();
        else if (type == Integer.TYPE)
            return Metamodel.BuiltinType.INT.name();
        else if (type == Double.TYPE)
            return Metamodel.BuiltinType.DOUBLE.name();
        else if (type == Long.TYPE)
            return Metamodel.BuiltinType.LONG.name();
        else if (type == Character.TYPE)
            return Metamodel.BuiltinType.LONG.name();
        else if (type == CompletableFuture.class) {
            return getOrFindTypeName(type.getTypeParameters()[0].getClass());
        } else if (type == List.class) {
            var subType = getOrFindTypeName(type.getTypeParameters()[0]);
            return subType + "[]";
        } else if (type == Class.class || type == Constructor.class || type == Proof.class) {
            throw new IllegalStateException("Forbidden class reached!");
        } else if (type instanceof Class<?>) {
            return type.getSimpleName();
        }
        return "<error>!!!??!?!?";
    }


    private Metamodel.@Nullable Type getOrFindType(Type genericReturnType) {
        switch (genericReturnType) {
            case GenericArrayType a ->
                throw new RuntimeException("Unwanted type found: " + genericReturnType);
            case Class<?> c -> {
                return getOrFindType(c);
            }
            case ParameterizedType pt -> {
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
            case null, default -> {
            }
        }

        return null;
    }
}
