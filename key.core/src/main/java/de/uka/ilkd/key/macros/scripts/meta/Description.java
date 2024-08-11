/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This annotation is used for the documentation of proof script commands.
 *
 * @author Mattias Ulbrich
 * @version 1
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface Description {
    /**
     * The textual description of the command. Used for documentation.
     *
     * @return a non-null string
     */
    String value();

    /**
     * Examples of how to use the command.
     *
     * @return concrete use case examples
     */
    String[] examples() default {};
}
