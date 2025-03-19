/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public final class ArgumentsLifter {
    // private static final Map<Class, Type> TYPE_MAP = new HashMap<>();

    private ArgumentsLifter() {
    }

    public static <T> List<ProofScriptArgument<T>> inferScriptArguments(Class<?> clazz,
            ProofScriptCommand<T> command) {
        List<ProofScriptArgument<T>> args = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            if (Modifier.isFinal(field.getModifiers())) {
                throw new UnsupportedOperationException(
                    "Proof script argument fields can't be final: " + field);
            }
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                args.add(lift(option, field));
            } else {
                Flag flag = field.getDeclaredAnnotation(Flag.class);
                if (flag != null) {
                    args.add(lift(flag, field));
                } else {
                    Varargs vargs = field.getDeclaredAnnotation(Varargs.class);
                    if (vargs != null) {
                        args.add(lift(vargs, field));
                    }
                }
            }
        }
        //
        args.forEach(a -> a.setCommand(command));
        return args;
    }

    private static <T> ProofScriptArgument<T> lift(Varargs vargs, Field field) {
        ProofScriptArgument<T> arg = new ProofScriptArgument<>();
        arg.setName(vargs.prefix());
        arg.setRequired(false);
        arg.setField(field);
        arg.setType(vargs.as());
        arg.setVariableArguments(true);
        return arg;
    }

    private static <T> ProofScriptArgument<T> lift(Option option, Field field) {
        ProofScriptArgument<T> arg = new ProofScriptArgument<>();
        arg.setName(option.value());
        arg.setRequired(option.required());
        arg.setField(field);
        arg.setType(field.getType());
        arg.setDocumentation(DescriptionFacade.getDocumentation(arg));
        return arg;
    }

    private static <T> ProofScriptArgument<T> lift(Flag flag, Field field) {
        throw new IllegalStateException("not implemented");
    }
}
