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
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.proof.Proof;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.description.JavadocDescription;
import com.github.javaparser.utils.SourceRoot;
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
    private final List<Metamodel.Type> types = new LinkedList<>();
    private final Metamodel.KeyApi keyApi = new Metamodel.KeyApi(endpoints, types);
    private final SourceRoot sourceRoot;

    public ExtractMetaData(Path source) {
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        config.setAttributeComments(true);
        config.setLexicalPreservationEnabled(false);
        config.setStoreTokens(false);
        config.setIgnoreAnnotationsWhenAttributingComments(true);
        config.setDoNotAssignCommentsPrecedingEmptyLines(true);
        sourceRoot = new SourceRoot(source, config);
    }

    @Override
    public void run() {
        for (Method method : KeyApi.class.getMethods()) {
            addServerEndpoint(method);
        }

        for (Method method : ClientApi.class.getMethods()) {
            addClientEndpoint(method);
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

    private String findDocumentation(Method method) {
        return findCompilationUnit(method.getDeclaringClass())
                .map(it -> it.getMethodsByName(method.getName()))
                .map(List::getFirst)
                .flatMap(NodeWithJavadoc::getJavadoc)
                .map(Javadoc::getDescription)
                .map(JavadocDescription::toText)
                .orElse("");
    }

    private List<Metamodel.Argument> translate(Parameter[] parameters) {
        return Arrays.stream(parameters).map(this::translate).toList();
    }

    private Metamodel.Argument translate(Parameter parameter) {
        var type = getOrFindType(parameter.getType()).name();
        return new Metamodel.Argument(parameter.getName(), type);
    }

    private Metamodel.Type getOrFindType(Class<?> type) {
        System.out.println(type);
        if (type == CompletableFuture.class) {
            return getOrFindType(type.getTypeParameters()[0].getClass());
        }

        if (type == List.class) {
            // TODO try to get the type below.
            var subType = getOrFindType(type.getTypeParameters()[0].getClass());
            return new Metamodel.ListType(subType, "");
        }

        if (type == Class.class || type == Constructor.class || type == Proof.class) {
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

        var t = types.stream().filter(it -> it.name().equals(type.getSimpleName())).findFirst();
        if (t.isPresent())
            return t.get();
        var a = createType(type);
        types.add(a);
        return a;
    }

    private Metamodel.Type createType(Class<?> type) {
        final var documentation = findDocumentation(type);
        if (type.isEnum())
            return new Metamodel.EnumType(type.getSimpleName(), type.getName(),
                Arrays.stream(type.getEnumConstants()).map(Object::toString).toList(),
                documentation);


        var obj = new Metamodel.ObjectType(type.getSimpleName(), type.getName(), new ArrayList<>(),
            documentation);
        final var list = Arrays.stream(type.getDeclaredFields())
                .map(it -> new Metamodel.Field(it.getName(), getOrFindType(it.getType()).name()))
                .toList();
        obj.fields().addAll(list);
        return obj;
    }

    private String findDocumentation(Class<?> type) {
        return findCompilationUnit(type)
                .flatMap(NodeWithJavadoc::getJavadocComment)
                .map(Comment::getContent)
                .orElse("");
    }

    private Optional<TypeDeclaration<?>> findCompilationUnit(Class<?> type) {
        try {
            return sourceRoot.parse(type.getPackageName(), type.getSimpleName() + ".java")
                    .getPrimaryType();
        } catch (ParseProblemException e) {
            return Optional.empty();
        }
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

    private Metamodel.@Nullable Type getOrFindType(Type genericReturnType) {
        if (genericReturnType instanceof Class<?> c)
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

    public Metamodel.KeyApi getApi() {
        return keyApi;
    }
}
