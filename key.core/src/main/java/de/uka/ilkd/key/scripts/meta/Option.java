/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This annotation marks key-value arguments in proof scripts parameter classes.
 * In contrast to a [Flag], an option receives an arbitrary value.
 *
 * @author Alexander Weigl
 * @version 1
 * @see Flag
 * @see Argument
 */
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Option {
    /**
     * Name of the command line argument.
     * If left blank, the name of the field is used.
     *
     * @return a non-null string
     * @see ProofScriptArgument
     */
    String value() default "";
}
