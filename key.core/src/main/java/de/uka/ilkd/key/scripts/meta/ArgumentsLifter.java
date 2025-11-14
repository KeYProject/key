/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.*;

import de.uka.ilkd.key.scripts.AbstractCommand;
import de.uka.ilkd.key.scripts.ProofScriptCommand;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
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
            if(!meta.isRequired() || meta.isFlag())
                sb.append("[");

            if (meta.isPositional()) {
                sb.append(OPEN_BRACKET + meta.getType().getSimpleName() + " (" + meta.getName() + ")" + CLOSE_BRACKET);
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
            
            if(!meta.isRequired() || meta.isFlag())
                sb.append("]");
        }


        return sb.toString();
    }

    public static String extractDocumentation(String command, Class<?> commandClazz,
            Class<?> parameterClazz) {
        StringBuilder sb = new StringBuilder();

        Deprecated dep = commandClazz.getAnnotation(Deprecated.class);
        if(dep != null) {
            sb.append("**Caution! This proof script command is deprecated, and may be removed soon!**\n\n");
        }

        Documentation docCommand = commandClazz.getAnnotation(Documentation.class);
        if (docCommand != null) {
            sb.append(docCommand.value());
            sb.append("\n\n");
        }

        if(parameterClazz == null) {
            return sb.toString();
        }

        Documentation docAn = parameterClazz.getAnnotation(Documentation.class);
        if (docAn != null) {
            sb.append(docAn.value());
            sb.append("\n\n");
        }

        sb.append("#### Usage: \n`").append(generateCommandUsage(command, parameterClazz))
                .append("`\n\n");

        List<ProofScriptArgument> args = getSortedProofScriptArguments(parameterClazz);

        sb.append("#### Parameters:\n");
        for (ProofScriptArgument meta : args) {
            sb.append("\n\n");
            if (meta.isPositional()) {
                sb.append("* `%s` *(%s%s positional argument, type %s)*:<br>%s".formatted(
                    meta.getName(),
                    meta.isRequired() ? "" : "optional ",
                    ordinalStr(meta.getArgumentPosition() + 1),
                    meta.getField().getType().getSimpleName(),
                    meta.getDocumentation()));
            }

            if (meta.isOption()) {
                sb.append("* `%s` *(%snamed option, type %s)*:<br>%s".formatted(
                    meta.getName(),
                    meta.isRequired() ? "" : "optional ",
                    meta.getField().getType().getSimpleName(),
                    meta.getDocumentation()));
            }

            if (meta.isFlag()) {
                sb.append("* `%s` *(flag)*:<br>%s".formatted(
                    meta.getName(),
                    meta.getDocumentation()));
            }

            if (meta.isPositionalVarArgs()) {
                sb.append("* `%s...` (%s): %s".formatted(
                    meta.getName(),
                    meta.getPositionalVarargs().as(),
                    meta.getPositionalVarargs().startIndex(),
                    meta.getDocumentation()));
            }

            if (meta.isOptionalVarArgs()) {
                sb.append("* `%s...`: *(options prefixed by `%s`, type %s)*:<br>%s".formatted(
                    meta.getName(), meta.getOptionalVarArgs().prefix(),
                    meta.getOptionalVarArgs().as().getSimpleName(),
                    meta.getDocumentation()));
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

    public static String extractCategory(Class<? extends ProofScriptCommand> commandClazz, @Nullable Class<?> parameterClazz) {
        Documentation docCommand = commandClazz.getAnnotation(Documentation.class);
        if (docCommand != null && !docCommand.category().isBlank()) {
            return docCommand.category();
        }

        if(parameterClazz != null) {
            Documentation docAn = parameterClazz.getAnnotation(Documentation.class);
            if (docAn != null && !docAn.category().isBlank()) {
                return docAn.category();
            }
        }

        return "Uncategorized";
    }


    private static @NonNull List<ProofScriptArgument> getSortedProofScriptArguments(
            Class<?> parameterClazz) {
//        Comparator<ProofScriptArgument> optional =
//            Comparator.comparing(ProofScriptArgument::isOption);
//        Comparator<ProofScriptArgument> positional =
//            Comparator.comparing(ProofScriptArgument::isPositional);
//        Comparator<ProofScriptArgument> flagal = Comparator.comparing(ProofScriptArgument::isFlag);
//        Comparator<ProofScriptArgument> allargsal =
//            Comparator.comparing(ProofScriptArgument::isPositionalVarArgs);
//        Comparator<ProofScriptArgument> byRequired =
//            Comparator.comparing(ProofScriptArgument::isRequired);
//        Comparator<ProofScriptArgument> byName = Comparator.comparing(ProofScriptArgument::getName);
//
//        Comparator<ProofScriptArgument> byPos = Comparator.comparing(it -> {
//            if (it.isPositionalVarArgs()) {
//                it.getPositionalVarargs().startIndex();
//            }
//            if (it.isPositional()) {
//                it.getArgument().value();
//            }
//
//            return -1;
//        });
//
//
//        var comp = optional
//                .thenComparing(flagal)
//                .thenComparing(positional)
//                .thenComparing(allargsal)
//                .thenComparing(byRequired)
//                .thenComparing(byPos)
//                .thenComparing(byName);

        var args = Arrays.stream(parameterClazz.getDeclaredFields())
                .map(ProofScriptArgument::new)
                .sorted(Comparator.comparing(ProofScriptArgument::orderString))
                .toList();
        return args;
    }

}
