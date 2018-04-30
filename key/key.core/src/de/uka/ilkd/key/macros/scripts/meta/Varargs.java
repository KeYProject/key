package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public @interface Varargs {
    Class as() default String.class;

    String prefix() default "";
}
