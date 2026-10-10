/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.scripts.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import de.uka.ilkd.key.scripts.ProofScriptCommand;

import com.github.therapi.runtimejavadoc.ClassJavadoc;
import com.github.therapi.runtimejavadoc.CommentFormatter;
import com.github.therapi.runtimejavadoc.RuntimeJavadoc;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Utility class for extracting metadata from proof script command annotations.
/// Generates usage documentation, parameter descriptions, and category information
/// from [@Documentation], [Argument], [Option], and [Flag] annotations.
///
/// @author Alexander Weigl
/// @version 1 (21.04.17)
public final class ArgumentsLifter {
    private static final String OPEN_BRACKET = "\u27e8";
    private static final String CLOSE_BRACKET = "\u27e9";

    private ArgumentsLifter() {
    }

    public static List<ProofScriptArgument> inferScriptArguments(Class<?> clazz) {
        List<ProofScriptArgument> args = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            if (Modifier.isFinal(field.getModifiers())) {
                throw new UnsupportedOperationException(
                    "Proof script argument fields can't be final: " + field);
            }
            ProofScriptArgument arg = new ProofScriptArgument(field);
            if (!arg.hasNoAnnotation()) {
                args.add(arg);
            }
        }
        return args;
    }

    public static String generateCommandUsage(String commandName, Class<?> parameterClazz) {
        final var args = getSortedProofScriptArguments(parameterClazz);
        var sb = new StringBuilder(commandName);
        for (var meta : args) {
            sb.append(' ');
            if (!meta.isRequired() || meta.isFlag())
                sb.append("[");

            if (meta.isPositional()) {
                sb.append(OPEN_BRACKET + meta.getType().getSimpleName() + " (" + meta.getName()
                    + ")" + CLOSE_BRACKET);
            }

            if (meta.isOption()) {
                sb.append(meta.getName());
                sb.append(":");
                sb.append(OPEN_BRACKET + meta.getField().getType().getSimpleName() + CLOSE_BRACKET);
            }

            if (meta.isFlag()) {
                sb.append(meta.getName());
            }

            if (meta.isPositionalVarArgs()) {
                sb.append("%s...".formatted(meta.getName()));
            }

            if (meta.isOptionalVarArgs()) {
                sb.append("%s...".formatted(meta.getName()));
            }

            if (!meta.isRequired() || meta.isFlag())
                sb.append("]");
        }


        return sb.toString();
    }

    public static String extractDocumentation(String command, Class<?> commandClazz,
            @Nullable Class<?> parameterClazz) {
        StringBuilder sb = new StringBuilder();

        Deprecated dep = commandClazz.getAnnotation(Deprecated.class);
        if (dep != null) {
            sb.append(
                "**Caution! This proof script command is deprecated, and may be removed soon!**\n\n");
        }

        ClassJavadoc jdocCommand = RuntimeJavadoc.getJavadoc(commandClazz);

        Documentation docCommand = commandClazz.getAnnotation(Documentation.class);
        if (docCommand != null) {
            sb.append(docCommand.value());
            sb.append("\n\n");
        } else if (jdocCommand != null && jdocCommand.getComment() != null) {
            // the javadoc is only available if the class was compiled with a JDK that
            // understands the doc comment style used in the source (e.g., JDK 23+ for ///)
            sb.append(jdocCommand.getComment());
            sb.append("\n\n");
        }

        if (parameterClazz == null) {
            return sb.toString();
        }

        ClassJavadoc jdocParams = RuntimeJavadoc.getJavadoc(parameterClazz);

        Documentation docAn = parameterClazz.getAnnotation(Documentation.class);
        if (docAn != null) {
            sb.append(docAn.value());
            sb.append("\n\n");
        } else if (jdocParams != null && jdocParams.getComment() != null) {
            sb.append(jdocParams.getComment());
            sb.append("\n\n");
        }


        sb.append("#### Usage: \n`").append(generateCommandUsage(command, parameterClazz))
                .append("`\n\n");

        List<ProofScriptArgument> args = getSortedProofScriptArguments(parameterClazz);

        sb.append("#### Parameters:\n");
        for (ProofScriptArgument meta : args) {
            sb.append("\n\n");

            var documentation = meta.getDocumentation();
            if (documentation.isEmpty() && jdocParams != null) {
                documentation = jdocParams.getFields().stream()
                        .filter(it -> it.getName().equals(meta.getField().getName()))
                        .findFirst()
                        .map(field -> new CommentFormatter().format(field.getComment()))
                        .orElse("");
            }

            if (meta.isPositional()) {
                sb.append("* `%s` *(%s%s positional argument, type %s)*:<br>%s".formatted(
                    meta.getName(),
                    meta.isRequired() ? "" : "optional ",
                    ordinalStr(meta.getArgumentPosition() + 1),
                    meta.getField().getType().getSimpleName(),
                    documentation));
            }

            if (meta.isOption()) {
                sb.append("* `%s` *(%snamed option, type %s)*:<br>%s".formatted(
                    meta.getName(),
                    meta.isRequired() ? "" : "optional ",
                    meta.getField().getType().getSimpleName(),
                    documentation));
            }

            if (meta.isFlag()) {
                sb.append("* `%s` *(flag)*:<br>%s".formatted(
                    meta.getName(),
                    documentation));
            }

            if (meta.isPositionalVarArgs()) {
                sb.append("* `%s...` (%s): %s<br>%s".formatted(
                    meta.getName(),
                    meta.getPositionalVarargs().as(),
                    meta.getPositionalVarargs().startIndex(),
                    documentation));
            }

            if (meta.isOptionalVarArgs()) {
                sb.append("* `%s...`: *(options prefixed by `%s`, type %s)*:<br>%s".formatted(
                    meta.getName(), meta.getOptionalVarArgs().prefix(),
                    meta.getOptionalVarArgs().as().getSimpleName(),
                    documentation));
            }

        }

        return sb.toString();
    }

    private static String ordinalStr(int post) {
        if (post % 100 >= 11 && post % 100 <= 13) {
            return post + "th";
        }
        return switch (post % 10) {
            case 1 -> post + "st";
            case 2 -> post + "nd";
            case 3 -> post + "rd";
            default -> post + "th";
        };
    }

    public static String extractCategory(Class<? extends ProofScriptCommand> commandClazz,
            @Nullable Class<?> parameterClazz) {
        Documentation docCommand = commandClazz.getAnnotation(Documentation.class);
        if (docCommand != null && !docCommand.category().isBlank()) {
            return docCommand.category();
        }

        if (parameterClazz != null) {
            Documentation docAn = parameterClazz.getAnnotation(Documentation.class);
            if (docAn != null && !docAn.category().isBlank()) {
                return docAn.category();
            }
        }

        return "Uncategorized";
    }


    private static @NonNull List<ProofScriptArgument> getSortedProofScriptArguments(
            Class<?> parameterClazz) {
        var args = Arrays.stream(parameterClazz.getDeclaredFields())
                .map(ProofScriptArgument::new)
                .sorted(Comparator.comparing(ProofScriptArgument::orderString))
                .toList();
        return args;
    }

}
