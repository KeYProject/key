/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;


import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/// Annotation for marking positional arguments of parameter classes.
///
/// @author Alexander Weigl
/// @version 1 (6/14/25)
@Retention(RetentionPolicy.RUNTIME)
public @interface Argument {
    /// Position of this argument in the positional argument list.
    ///
    /// @return a non-null string
    /// @see ScriptCommandAst#positionalArgs()
    int value() default 0;
}
