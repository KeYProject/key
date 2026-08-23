/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.util.Arrays;
import java.util.List;

import com.github.therapi.runtimejavadoc.ClassJavadoc;
import com.github.therapi.runtimejavadoc.MethodJavadoc;
import com.github.therapi.runtimejavadoc.ParamJavadoc;
import com.github.therapi.runtimejavadoc.RuntimeJavadoc;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// Describes a single "variable condition" (varcond) or taclet-builder command that can be
/// used inside taclet definitions, together with metadata needed to parse, validate, and
/// document its usage.
///
/// An instance of this interface bundles together:
///
/// - the command's [`name`][#name()] as it appears in taclet source files,
/// - the expected [`argument types`][#argumentTypes()],
/// - whether the command [`supports negation`][#isNegationSupported()] (i.e. an
/// additional trailing `boolean` constructor argument),
/// - and Javadoc-derived documentation for both the command itself and its individual
/// arguments, extracted via reflection from the backing implementation class.
///
/// Instances are typically created via the [#createVarcondInfo] factory methods rather
/// than by implementing this interface directly.
///
/// @author Alexander Weigl
/// @version 1 (23.08.26)
@NullMarked
public interface TacletBuilderCommandInfo {

    /// Returns the name of this command as used in taclet source files.
    ///
    /// @return the command name, never `null`
    String name();

    /// Returns the declared types of the arguments accepted by this command, in the order
    /// they must appear in the taclet source.
    ///
    /// @return the array of argument types
    ArgumentType[] argumentTypes();

    /// Returns the names of the arguments as declared in the backing implementation's
    /// constructor (or as documented via Javadoc, if available).
    ///
    /// Resolving the argument names requires reflecting on the implementation class and is
    /// performed lazily on first access.
    ///
    /// @return the array of argument names, in the same order as [#argumentTypes()]
    String[] argNames();

    /// Indicates whether this command supports an optional trailing negation flag, i.e.
    /// whether the backing implementation class has a constructor whose parameters are the
    /// declared [`argument types`][#argumentTypes()] followed by an additional
    /// `boolean` parameter.
    ///
    /// @return `true` if negation is supported, `false` otherwise
    boolean isNegationSupported();

    /// Returns the class-level Javadoc documentation extracted from the backing
    /// implementation class. This is typically used as the general description of what the
    /// command does.
    ///
    /// @return the class-level Javadoc, never `null`
    ClassJavadoc getGeneralDocumentation();

    /// Returns the Javadoc documentation of the specific constructor that matches this
    /// command's argument types (and negation flag, if supported). This is typically used
    /// to document the individual arguments of the command.
    ///
    /// @return the matching constructor's Javadoc, or a documentation object with empty
    /// fields if no Javadoc could be resolved
    MethodJavadoc getArgumentInformation();

    /// Creates a [TacletBuilderCommandInfo] for a command whose negation support is
    /// determined automatically by inspecting the constructors of `clazz`.
    ///
    /// @param name the name of the command as used in taclet source files
    /// @param clazz the implementation class backing this command
    /// @param types the expected argument types, in declaration order
    /// @return a new [TacletBuilderCommandInfo] instance
    static TacletBuilderCommandInfo createVarcondInfo(String name, Class<?> clazz,
            ArgumentType... types) {
        return new TacletBuilderCommandInfoImpl(name, types, clazz, null);
    }

    /// Creates a [TacletBuilderCommandInfo] for a command with an explicitly specified
    /// negation support flag, instead of determining it via reflection.
    ///
    /// @param name the name of the command as used in taclet source files
    /// @param clazz the implementation class backing this command
    /// @param negationSupported whether the command supports a trailing negation argument
    /// @param types the expected argument types, in declaration order
    /// @return a new [TacletBuilderCommandInfo] instance
    static TacletBuilderCommandInfo createVarcondInfo(String name, Class<?> clazz,
            Boolean negationSupported, ArgumentType... types) {
        return new TacletBuilderCommandInfoImpl(name, types, clazz, negationSupported);
    }
}


/// Default implementation of [TacletBuilderCommandInfo].
///
/// Argument names and documentation are resolved lazily, on first access, by reflecting on
/// the backing implementation class ([#clazz]) and looking up its runtime Javadoc via
/// [RuntimeJavadoc].
class TacletBuilderCommandInfoImpl implements TacletBuilderCommandInfo {
    /// The name of the command as used in taclet source files.
    public final String name;
    /// The expected argument types, in declaration order.
    private final ArgumentType[] argTypes;
    /// The implementation class backing this command, used for reflection-based lookups.
    private final Class<?> clazz;
    /// Whether this command supports a trailing negation argument. `null` until
    /// lazily resolved via [#isNegationSupported()].
    private @Nullable Boolean isNegationSupported;
    /// The resolved argument names, or `null` until [#findDocumentation()] has run.
    private String @Nullable [] argNames;
    /// The resolved class-level Javadoc, or `null` until [#findDocumentation()] has run.
    private @Nullable ClassJavadoc generalDocumentation;
    /// The resolved constructor Javadoc, or `null` until [#findDocumentation()] has run.
    private @Nullable MethodJavadoc argumentDocumentation;

    /// Creates a new command descriptor.
    ///
    /// @param name the name of the command as used in taclet source files
    /// @param types the expected argument types, in declaration order
    /// @param clazz the implementation class backing this command
    /// @param negationSupported whether the command supports a trailing negation argument,
    /// or `null` to determine this lazily via reflection
    public TacletBuilderCommandInfoImpl(String name, ArgumentType[] types, Class<?> clazz,
            @Nullable Boolean negationSupported) {
        this.name = name;
        argTypes = types;
        this.clazz = clazz;
        isNegationSupported = negationSupported;
    }

    @Override
    public String name() {
        return name;
    }

    @Override
    public ArgumentType[] argumentTypes() {
        return argTypes;
    }

    @Override
    public String[] argNames() {
        if (argNames == null) {
            findDocumentation();
        }
        return argNames;
    }

    @Override
    public boolean isNegationSupported() {
        if (isNegationSupported == null) {
            isNegationSupported = lastArgumentOfFirstConstructorIsBoolean(clazz, argTypes);
        }
        return isNegationSupported;
    }

    @Override
    public ClassJavadoc getGeneralDocumentation() {
        if (generalDocumentation == null) {
            findDocumentation();
        }
        return generalDocumentation;
    }

    @Override
    public MethodJavadoc getArgumentInformation() {
        if (argumentDocumentation == null) {
            findDocumentation();
        }
        return argumentDocumentation;
    }

    /// Computes the parameter types of the constructor that this command's arguments (and,
    /// if applicable, its negation flag) would map to.
    ///
    /// @return the array of expected constructor parameter types
    Class<?>[] getConstructorClasses() {
        return getConstructorClasses(argTypes, isNegationSupported == Boolean.TRUE);
    }

    /// Resolves and caches [#argNames], [#generalDocumentation], and
    /// [#argumentDocumentation] by reflecting on [#clazz] and looking up its
    /// matching constructor's runtime Javadoc.
    ///
    /// If no constructor matching [#getConstructorClasses()] can be found, argument
    /// names are filled with empty strings and empty documentation placeholders are used
    /// instead of failing.
    private void findDocumentation() {
        ClassJavadoc classDoc = RuntimeJavadoc.getJavadoc(clazz.getName());
        generalDocumentation = classDoc;

        try {
            var constr = clazz.getConstructor(getConstructorClasses());
            final var constructorDeclaration = classDoc.getConstructors()
                    .stream().filter(it -> it.matches(constr)).findAny();

            final var parameters = constr.getParameters();
            argNames = new String[argTypes.length];
            for (int i = 0; i < argTypes.length; i++) {
                argNames[i] = parameters[i].getName();
            }

            constructorDeclaration.ifPresent(it -> {
                List<ParamJavadoc> params = it.getParams();
                for (int i = 0; i < params.size(); i++) {
                    argNames[i] = params.get(i).getName();
                }
            });

            argumentDocumentation = constructorDeclaration
                    .orElse(new MethodJavadoc(constr.getName(), null, null, null, null, null, null,
                        null));
        } catch (NoSuchMethodException e) {
            argNames = new String[argTypes.length];
            Arrays.fill(argNames, "");
            argumentDocumentation = new MethodJavadoc("", null, null, null, null, null, null, null);
        }
        // endregion
    }


    /// Checks whether `clazz` declares a constructor whose parameter types are
    /// `argTypes` followed by a trailing `boolean` parameter, which indicates
    /// support for an optional negation flag.
    ///
    /// @param clazz the implementation class to inspect
    /// @param argTypes the expected leading argument types
    /// @return `true` if such a constructor exists, `false` otherwise
    private static boolean lastArgumentOfFirstConstructorIsBoolean(
            Class<?> clazz, ArgumentType[] argTypes) {
        if (findConstructor(clazz, getConstructorClasses(argTypes, true))) {
            return true;
        }
        if (findConstructor(clazz, getConstructorClasses(argTypes, false))) {
            return false;
        }
        throw new IllegalStateException();
    }

    private static boolean findConstructor(Class<?> clazz, Class<?>[] constructorClasses) {
        final var constructors = clazz.getConstructors();
        c: for (var constructor : constructors) {
            if (constructor.getParameterCount() != constructorClasses.length)
                continue c;
            final var parameterTypes = constructor.getParameterTypes();
            for (var i = 0; i < parameterTypes.length; i++) {
                if (!constructorClasses[i].isAssignableFrom(parameterTypes[i])) {
                    continue c;
                }
            }
            return true;
        }
        return false;
    }

    /// Builds the array of constructor parameter types corresponding to `argTypes`,
    /// optionally appending `boolean.class` for negation support.
    ///
    /// @param argTypes the declared argument types
    /// @param isNegationSupported whether a trailing `boolean` parameter should be
    /// appended for negation support
    /// @return the resulting array of constructor parameter types
    static Class<?>[] getConstructorClasses(ArgumentType[] argTypes, boolean isNegationSupported) {
        Class<?>[] clazzes = new Class[argTypes.length + (isNegationSupported ? 1 : 0)];
        for (int i = 0; i < argTypes.length; i++) {
            clazzes[i] = argTypes[i].clazz;
        }

        if (isNegationSupported)
            clazzes[clazzes.length - 1] = Boolean.TYPE;
        return clazzes;
    }

}
