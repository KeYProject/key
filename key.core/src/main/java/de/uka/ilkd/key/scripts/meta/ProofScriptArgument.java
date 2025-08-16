/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.lang.reflect.Field;
import java.util.Objects;

import org.checkerframework.checker.nullness.qual.EnsuresNonNull;
import org.jspecify.annotations.Nullable;

/// This class captures the meta data about parameters of [ProofScriptCommand]s.
///
/// The meta information are found by various annotations.
///
/// @author Alexander Weigl
/// @version 1 (21.04.17)
/// @see Flag
/// @see Option
/// @see PositionalVarargs
/// @see OptionalVarargs
/// @see Argument
public class ProofScriptArgument {
    private final Field field;
    private final @Nullable Flag flag;
    private final @Nullable Option option;
    private final @Nullable Argument argument;
    private final @Nullable PositionalVarargs positionalVarargs;
    private final @Nullable OptionalVarargs optionalVarargs;

    public ProofScriptArgument(Field field) {
        this.field = field;

        this.flag = field.getAnnotation(Flag.class);
        this.option = field.getAnnotation(Option.class);
        this.argument = field.getAnnotation(Argument.class);
        this.optionalVarargs = field.getAnnotation(OptionalVarargs.class);
        this.positionalVarargs = field.getAnnotation(PositionalVarargs.class);
    }

    /// The supplied name of this parameter, either by annotation or name of the field.
    public String getName() {
        if (flag != null && !flag.value().isBlank()) {
            return flag.value();
        }
        if (option != null && !option.value().isBlank()) {
            return option.value();
        }
        return field.getName();
    }

    /// True if this field should be set on every call by the user
    /// iff a non-null value should be ensured.
    public boolean isRequired() {
        final var annotatedType = field.getAnnotatedType();
        return annotatedType.getAnnotation(Nullable.class) == null;
        // || annotatedType.getAnnotation(MonotonicNonNull.class) != null;
    }

    /// True if this argument is a boolean flag.
    public boolean isFlag() {
        return flag != null;
    }

    /// The underlying Java field.
    public Field getField() {
        return field;
    }

    /// Documentation of this argument provided by {@link Documentation}.
    ///
    /// @see Documentation
    public String getDocumentation() {
        if (field.getAnnotation(Documentation.class) != null) {
            return field.getAnnotation(Documentation.class).value();
        }
        return "";
    }

    /// True if this argument captures positional variable arguments.
    @EnsuresNonNull("positionalVarargs")
    public boolean isPositionalVarArgs() {
        return positionalVarargs != null;
    }

    /// True if this argument captures positional key-value arguments.
    @EnsuresNonNull("optionalVarargs")
    public boolean isOptionalVarArgs() {
        return optionalVarargs != null;
    }

    /// True if this argument is a positional argument (w/o a keyword).
    @EnsuresNonNull("argument")
    public boolean isPositional() {
        return argument != null;
    }

    /// The index number of a positional argument.
    ///
    /// @see #isPositional()
    public int getArgumentPosition() {
        return Objects.requireNonNull(argument).value();
    }

    /// True if this argument is a key-value parameter.
    public boolean isOption() {
        return option != null;
    }

    /// True if this field has at least one necessary annotation and should be considered as a valid
    /// parameter.
    public boolean hasNoAnnotation() {
        return !isFlag() && !isOption() && !isPositionalVarArgs() && !isPositional()
                && !isOptionalVarArgs();
    }

    /// Returns the flag metadata.
    public @Nullable Flag getFlag() {
        return flag;
    }

    /// Returns the key-value varargs metadata.
    public @Nullable OptionalVarargs getOptionalVarArgs() {
        return this.optionalVarargs;
    }

    /// Returns the positional varargs metadata.
    public @Nullable PositionalVarargs getPositionalVarargs() {
        return this.positionalVarargs;
    }

    /// Returns the positional metadata.
    public @Nullable Argument getArgument() {
        return argument;
    }

    /// Returns the data type of the underlying field.
    public Class<?> getType() {
        return field.getType();
    }
}
