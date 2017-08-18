package de.uka.ilkd.key.macros.scripts.meta;

/**
 * Currently not implemented in {@link ArgumentsLifter}
 *
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 * @see Option
 */
public @interface Flag {
    /**
     * @return
     */
    String arg();

    /**
     * @return
     */
    String value();

    /**
     * @return
     */
    String help() default "";
}
