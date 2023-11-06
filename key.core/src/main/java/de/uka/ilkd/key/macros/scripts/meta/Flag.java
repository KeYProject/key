/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

// Need to switch spotless off for the comment because it replaces @Flag with &#64;Flag
// spotless:off
/**
 * Currently not implemented in {@link ArgumentsLifter}
 * <p>
 * Used to mark flag for proof script commands. For example "instantitate formula='...' ... hide" is
 * denoted as
 * </p>
 * <p>
 *
 * <pre>
 * {@code
 *  @Flag(name="hide"}
 *  boolean hideFormula.
 * }
 * </pre>
 * </p>
 * <p>
 * Only applicable to boolean fields!
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 * @see Option
 */
//spotless:on
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
