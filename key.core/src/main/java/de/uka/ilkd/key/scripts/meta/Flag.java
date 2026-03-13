/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

// Need to switch spotless off for the comment because it replaces @Flag with &#64;Flag
// spotless:off

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// An annotation for marking flag (boolean) arguments of proof script commands.
/// For example `instantiate formula='...' ... hide` has a flag `hide`.
/// denoted as
///
/// ```java
/// class Parameters {
/// boolean @Flag hide; ...
/// }
/// ```
///
/// Only applicable to boolean fields! Value can be passed as named argument `hide=true` or
/// `hide=false` or
/// as positional argument ` ... hide;`.
///
/// @author Alexander Weigl
/// @version 1 (21.04.17)
/// @see Option
/// @see ArgumentsLifter
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Flag {
    /**
     * Name of the command line argument.
     * If left blank, the name of the field is used.
     *
     * @return a non-null string
     */
    String value() default "";

    /**
     * The default value of this flag.
     *
     * @return true iff this field is required (not null)
     */
    boolean defValue() default false;
}
