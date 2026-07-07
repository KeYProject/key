/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

// @formatter:off
/// Annotation for capturing variable-length positional arguments.
/// Collects all remaining positional arguments starting from a given index.
///
/// ## Usage Example
/// ```java
/// class Parameters {
///   @Argument(0)
///   String firstArg;
///
/// @PositionalVarargs(as = String.class, startIndex = 1)
///   List<String> remainingArgs;
/// }
/// ```
///
/// @author Alexander Weigl
/// @version 1 (02.05.17)
// @formatter:on

@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface PositionalVarargs {

    /// The target type to convert each positional argument to.
    /// @return the element type of the varargs collection
    Class<?> as() default String.class;

    /// The index at which to start collecting positional arguments.
    /// All arguments from this index onward are captured.
    /// @return the starting index (0-based)
    int startIndex() default 0;
}
