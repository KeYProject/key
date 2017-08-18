package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This annotation is used for annotation of proof scripts arguments.
 *
 * @author Alexander Weigl
 * @version 1
 */
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Option {
    /**
     * Name of the command line argument.
     */
    String value();

    /**
     * Marks if this option has to be given on call of corresponding script command.
     */
    boolean required() default true;

    /**
     * A help message for this argument.
     * @return
     */
    String help() default "";
}
