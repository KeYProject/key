package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public final class ArgumentsLifter {
    //private static final Map<Class, Type> TYPE_MAP = new HashMap<>();

    private ArgumentsLifter() {
    }

    public static List<ProofScriptArgument>
                    inferScriptArguments(Class<?> clazz,
                                         ProofScriptCommand<?> command) {
        List<ProofScriptArgument> args = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                args.add(lift(option, field));
            }
            else {
                Flag flag = field.getDeclaredAnnotation(Flag.class);
                if (flag != null) {
                    args.add(lift(flag, field));
                }
                else {
                    Varargs vargs = field.getDeclaredAnnotation(Varargs.class);
                    if (vargs!=null) {
                        args.add(lift(vargs, field));
                    }
                }
            }
        }
        //
        args.forEach(a -> a.setCommand(command));
        return args;
    }

    private static ProofScriptArgument<?> lift(Varargs vargs, Field field) {
        ProofScriptArgument<?> arg = new ProofScriptArgument<Object>();
        arg.setName(vargs.prefix());
        arg.setRequired(false);
        arg.setField(field);
        arg.setType(vargs.as());
        arg.setVariableArguments(true);
        return arg;
    }

    private static ProofScriptArgument<?> lift(Option option, Field field) {
        ProofScriptArgument<?> arg = new ProofScriptArgument<Object>();
        arg.setName(option.value());
        arg.setRequired(option.required());
        arg.setField(field);
        arg.setType(field.getType());
        arg.setDocumentation(DescriptionFacade.getDocumentation(arg));
        return arg;
    }

    private static ProofScriptArgument<?> lift(Flag flag, Field field) {
        throw new IllegalStateException("not implemented");
    }
}