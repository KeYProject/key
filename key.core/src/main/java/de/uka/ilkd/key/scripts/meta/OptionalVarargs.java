/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// This annotation marks a catch-all parameter for key-value arguments.
/// It needs to be applied on an [java.util.Map] from [String] to class `T` as given
/// in [#as()].
/// It is possible to have multiple [OptionalVarargs]
/// that differentiate by name and by type.
///
/// @author Alexander Weigl
/// @version 1 (02.05.17)
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface OptionalVarargs {
    /// Target type of the [Map]. Defaults to [String].
    Class<?> as() default String.class;

    /// Prefix of the keys. For example, "inst_" captures all key-values starting with "inst_".
    String prefix() default "";
}
