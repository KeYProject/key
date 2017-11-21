package de.uka.ilkd.key.macros.scripts.meta;

/**
 * Currently not implemented in {@link ArgumentsLifter}
 * <p>
 * Used to mark flag for proof script commands.
 * For example "instantitate formula='...' ... hide" is denoted as
 * <p>
 * <code><pre>
 * @Flag(name="hide"}
 * boolean hideFormula.
 * </pre></code>
 * <p>
 * Only applicable to boolean fields!
 *
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 * @see Option
 */
public @interface Flag {
    /**
     * Name of the command line argument.
     *
     * @return a non-null string
     */
    String value();

    /**
     * The default value of this flag.
     *
     * @return true iff this field is required (not null)
     */
    boolean defValue() default false;

    /**
     * A help message for this argument.
     *
     * @return a non-null string
     */
    String help() default "";

}
