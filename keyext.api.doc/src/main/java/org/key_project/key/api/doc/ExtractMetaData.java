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
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.api.doc.Metamodel.HelpText;
import org.key_project.key.api.doc.Metamodel.HelpTextEntry;

import com.github.therapi.runtimejavadoc.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.jspecify.annotations.Nullable;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteclient.ClientApi;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */

public class ExtractMetaData implements Runnable {
    private final List<Metamodel.Endpoint> endpoints = new LinkedList<>();
    private final Map<Class<?>, Metamodel.Type> types = new HashMap<>();
    private final Map<String, HelpText> segDocumentation = new TreeMap<>();
    private final Metamodel.KeyApi keyApi =
        new Metamodel.KeyApi(endpoints, types, segDocumentation);

    public ExtractMetaData() {
    }

    @Override
    public void run() {
        for (Method method : KeyApi.class.getMethods()) {
            addServerEndpoint(method);
        }

        for (Method method : ClientApi.class.getMethods()) {
            addClientEndpoint(method);
        }

        for (var anInterface : KeyApi.class.getInterfaces()) {
            var js = anInterface.getAnnotation(JsonSegment.class);
            if (js != null) {
                var key = js.value();
                var doc = findDocumentation(anInterface);
                segDocumentation.put(key, doc);
            }
        }
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

    private @Nullable HelpText findDocumentation(Method method) {
        MethodJavadoc javadoc = RuntimeJavadoc.getJavadoc(method);
        if (javadoc.isEmpty())
            return null;

        final var visitor = new ToHtmlStringCommentVisitor();
        javadoc.getComment().visit(visitor);

        var t = javadoc.getThrows().stream()
                .map(it -> new HelpTextEntry(it.getName(), it.getComment().toString()));

        var p = javadoc.getParams().stream()
                .map(it -> new HelpTextEntry(it.getName(), it.getComment().toString()));

        var r = Stream.of(new HelpTextEntry("returns", javadoc.getReturns().toString()));

        return new HelpText(visitor.build(),
            Stream.concat(r, Stream.concat(p, t)).toList());
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
            return new Metamodel.ListType(subType);
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
        if (type.isEnum()) {
            return new Metamodel.EnumType(type.getSimpleName(), type.getName(),
                Arrays.stream(type.getEnumConstants())
                        .map(
                            it -> new Metamodel.EnumConstant(it.toString(),
                                findDocumentationEnum(type, it)))
                        .toList(),
                documentation);
        }

        var obj = new Metamodel.ObjectType(type.getSimpleName(), type.getName(), new ArrayList<>(),
            documentation);
        final var list = Arrays.stream(type.getDeclaredFields())
                .map(it -> new Metamodel.Field(it.getName(), getOrFindTypeName(it.getGenericType()),
                    type.isRecord()
                            ? findDocumentationRecord(type, it.getName())
                            : findDocumentation(it)))
                .toList();
        obj.fields().addAll(list);
        return obj;
    }

    private @Nullable HelpText findDocumentation(Field it) {
        var javadoc = RuntimeJavadoc.getJavadoc(it);
        if (javadoc.isEmpty())
            return null;
        return printFieldDocumentation(javadoc);
    }

    private @Nullable HelpText findDocumentationEnum(Class<?> type, Object enumConstant) {
        ClassJavadoc javadoc = RuntimeJavadoc.getJavadoc(type);
        if (javadoc.isEmpty())
            return null;
        for (var cdoc : javadoc.getEnumConstants()) {
            if (cdoc.getName().equalsIgnoreCase(enumConstant.toString())) {
                return printFieldDocumentation(cdoc);
            }
        }
        return null;
    }

    private @Nullable HelpText findDocumentationRecord(Class<?> type, String name) {
        ClassJavadoc javadoc = RuntimeJavadoc.getJavadoc(type);
        if (javadoc.isEmpty())
            return null;
        for (var cdoc : javadoc.getRecordComponents()) {
            if (cdoc.getName().equalsIgnoreCase(name)) {
                return new HelpText(cdoc.getComment().toString(), List.of());
            }
        }
        return null;
    }

    private static HelpText printFieldDocumentation(FieldJavadoc javadoc) {
        final var visitor = new ToHtmlStringCommentVisitor();
        javadoc.getComment().visit(visitor);

        var t = javadoc.getOther().stream()
                .map(it -> new HelpTextEntry(it.getName(), it.getComment().toString()));

        var p = javadoc.getSeeAlso().stream().map(
            it -> new HelpTextEntry(it.getSeeAlsoType().toString(), it.getStringLiteral()));

        return new HelpText(visitor.build(), Stream.concat(p, t).toList());
    }

    private @Nullable HelpText findDocumentation(Class<?> type) {
        ClassJavadoc classDoc = RuntimeJavadoc.getJavadoc(type);
        if (!classDoc.isEmpty()) { // optionally skip absent documentation
            var other = classDoc.getOther()
                    .stream().map(it -> new HelpTextEntry(it.getName(),
                        it.getComment().toString()));
            var also = classDoc.getSeeAlso()
                    .stream().map(it -> new HelpTextEntry(it.getSeeAlsoType().toString(),
                        it.getStringLiteral()));

            return new HelpText(
                classDoc.getComment().toString(),
                Stream.concat(other, also).toList());
        }
        return null;
    }

    private void addClientEndpoint(Method method) {
        var jsonSegment = method.getDeclaringClass().getAnnotation(JsonSegment.class);
        var segment = jsonSegment == null ? "" : jsonSegment.value();

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

    private static String callMethodName(String method, String segment,
            @Nullable String userValue,
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
                    return new Metamodel.ListType(base);
                }

                if (Objects.equals(pt.getRawType().getTypeName(), Either.class.getTypeName())) {
                    var base1 = getOrFindType(pt.getActualTypeArguments()[0]);
                    var base2 = getOrFindType(pt.getActualTypeArguments()[1]);
                    return new Metamodel.EitherType(base1, base2);
                }
            }
            default -> {
            }
        }

        return null;
    }

    public Metamodel.KeyApi getApi() {
        return keyApi;
    }
}
