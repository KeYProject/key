/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public final class ArgumentsLifter {
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
            sb.append(meta.isRequired() ? '<' : '[');

            if (meta.isPositional()) {
                sb.append(meta.getName());
            }

            if (meta.isOption()) {
                sb.append(meta.getName());
                sb.append(": ");
                sb.append(meta.getField().getType().getName());
            }

            if (meta.isFlag()) {
                sb.append(meta.getName());
                sb.append("[: true/false]");
            }

            if (meta.isPositionalVarArgs()) {
                sb.append("%s...".formatted(meta.getName()));
            }

            if (meta.isOptionalVarArgs()) {
                sb.append("%s...".formatted(meta.getName()));
            }

            sb.append(meta.isRequired() ? '>' : ']');
        }


        return sb.toString();
    }

    public static String extractDocumentation(String command, Class<?> commandClazz,
            Class<?> parameterClazz) {
        StringBuilder sb = new StringBuilder();

        Documentation docCommand = commandClazz.getAnnotation(Documentation.class);
        if (docCommand != null) {
            sb.append(docCommand.value());
            sb.append("\n\n");
        }

        Documentation docAn = parameterClazz.getAnnotation(Documentation.class);
        if (docAn != null) {
            sb.append(docAn.value());
            sb.append("\n\n");
        }

        sb.append("Usage: ").append(generateCommandUsage(command, parameterClazz))
                .append("\n\n");

        final var args = getSortedProofScriptArguments(parameterClazz);

        for (var meta : args) {
            sb.append("\n\n");
            if (meta.isPositional()) {
                sb.append("* Argument %s (%s): %s".formatted(
                    meta.getName(),
                    meta.getField().getType(),
                    meta.getDocumentation()));
            }

            if (meta.isOption()) {
                sb.append("* Option %s (%s): %s".formatted(
                    meta.getName(),
                    meta.getField().getType(),
                    meta.getDocumentation()));
            }

            if (meta.isFlag()) {
                sb.append("* Option %s [%s]: %s".formatted(
                    meta.getName(),
                    meta.getFlag().defValue(),
                    meta.getDocumentation()));
            }

            if (meta.isPositionalVarArgs()) {
                sb.append("* %s... (%s): %s".formatted(
                    meta.getName(),
                    meta.getPositionalVarargs().as(),
                    meta.getPositionalVarargs().startIndex(),
                    meta.getDocumentation()));
            }

            if (meta.isOptionalVarArgs()) {
                sb.append("* %s: %s... (%s): %s".formatted(
                    meta.getOptionalVarArgs(),
                    meta.getName(),
                    meta.getField().getType(),
                    meta.getDocumentation()));
            }

        }

        return sb.toString();
    }

    private static @NonNull List<ProofScriptArgument> getSortedProofScriptArguments(
            Class<?> parameterClazz) {
        Comparator<ProofScriptArgument> optional =
            Comparator.comparing(ProofScriptArgument::isOption);
        Comparator<ProofScriptArgument> positional =
            Comparator.comparing(ProofScriptArgument::isPositional);
        Comparator<ProofScriptArgument> flagal = Comparator.comparing(ProofScriptArgument::isFlag);
        Comparator<ProofScriptArgument> allargsal =
            Comparator.comparing(ProofScriptArgument::isPositionalVarArgs);
        Comparator<ProofScriptArgument> byRequired =
            Comparator.comparing(ProofScriptArgument::isRequired);
        Comparator<ProofScriptArgument> byName = Comparator.comparing(ProofScriptArgument::getName);

        Comparator<ProofScriptArgument> byPos = Comparator.comparing(it -> {
            if (it.isPositionalVarArgs()) {
                it.getPositionalVarargs().startIndex();
            }
            if (it.isPositional()) {
                it.getArgument().value();
            }

            return -1;
        });


        var comp = optional
                .thenComparing(flagal)
                .thenComparing(positional)
                .thenComparing(allargsal)
                .thenComparing(byRequired)
                .thenComparing(byPos)
                .thenComparing(byName);

        var args = Arrays.stream(parameterClazz.getDeclaredFields())
                .map(ProofScriptArgument::new)
                .sorted(comp)
                .toList();
        return args;
    }

}
