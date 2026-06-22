/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// This annotation is used for documenting proof script commands and their arguments.
///
/// It can be applied to command classes to provide overall documentation and categorization,
/// or to parameter fields within command parameter classes to document individual arguments.
///
/// The documentation is extracted at runtime via reflection by [ArgumentsLifter] to generate
/// usage help, parameter descriptions, and category groupings for the UI.
///
/// This annotation is also processed by [DocumentationGenerator] to automatically
/// generate comprehensive Markdown documentation for all proof script commands.
///
/// ## Examples
///
/// On a command class:
/// ```java
/// @Documentation(category = "Fundamental", value = """
/// The command "focus" allows you to select formulas from the current sequent...
/// """)
/// static class Parameters { ... }
/// ```
///
/// On a parameter field:
/// ```java
/// @Argument
/// @Documentation("The sequent containing the formulas to keep.")
/// public SequentWithHoles toKeep;
/// ```
///
/// @author Mattias Ulbrich
/// @version 1
/// @see ArgumentsLifter#extractDocumentation(String, Class, Class)
/// @see ArgumentsLifter#extractCategory(Class, Class)
/// @see ProofScriptArgument#getDocumentation()
/// @see DocumentationGenerator in the test sources for to generate
/// documentation (for the doc webapage).

@Target({ ElementType.TYPE, ElementType.FIELD })
@Retention(RetentionPolicy.RUNTIME)
public @interface Documentation {
    /// The main documentation text for the command or argument.
    /// Supports multi-line strings and markdown formatting.
    /// @return a non-null documentation string
    String value();

    /// The category name for grouping commands in the UI or documentation.
    /// Common categories include "Fundamental", "Control", "Internal", and "JML".
    /// @return a category name (may be empty)
    String category() default "";
}
