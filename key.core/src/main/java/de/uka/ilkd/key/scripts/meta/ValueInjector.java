/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.scripts.ProofScriptCommand;
import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (29.03.17)
 */
public class ValueInjector {
    /**
     * A default instance
     *
     * @see #getInstance()
     */
    private static @MonotonicNonNull ValueInjector instance;

    /**
     * A mapping between desired types and suitable @{@link Converter}.
     * <p>
     * Should be
     *
     * <pre>
     * T --> StringConverter<T>
     * </pre>
     */
    private final Map<ConverterKey<?, ?>, Converter<?, ?>> converters = new HashMap<>();

    /**
     * @param source
     * @param target
     * @param <S>
     * @param <T>
     */
    private record ConverterKey<S, T>(
            Class<S> source, Class<T> target) {
    }

    /**
     * Injects the given {@code arguments} in the {@code obj}. For more details see
     * {@link #inject(Object, ScriptCommandAst)}
     *
     * @param command a proof script command
     * @param obj a parameter class with annotation
     * @param arguments a non-null map of string pairs
     * @param <T> an arbitrary type
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException an access on some reflection methods occurred
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException an converter could not translate the given value in arguments
     */
    public static <T> T injection(ProofScriptCommand command, @NonNull T obj,
            ScriptCommandAst arguments) throws ArgumentRequiredException,
            InjectionReflectionException, NoSpecifiedConverterException, ConversionException {
        return getInstance().inject(obj, arguments);
    }

    /**
     * Returns the default instance of a {@link ValueInjector} Use with care. No multi-threading.
     *
     * @return a static reference to the default converter.
     * @see #createDefault()
     */
    public static ValueInjector getInstance() {
        if (instance == null) {
            instance = createDefault();
        }
        return instance;
    }

    /**
     * Returns a fresh instance of a {@link ValueInjector} with the support for basic primitive data
     * types.
     *
     * @return a fresh instance
     */
    public static ValueInjector createDefault() {
        ValueInjector vi = new ValueInjector();
        vi.addConverter(Integer.class, String.class, Integer::parseInt);
        vi.addConverter(Long.class, String.class, Long::parseLong);
        vi.addConverter(Boolean.class, String.class, Boolean::parseBoolean);
        vi.addConverter(Double.class, String.class, Double::parseDouble);
        vi.addConverter(String.class, String.class, (String s) -> s);
        vi.addConverter(Boolean.TYPE, String.class, Boolean::parseBoolean);
        vi.addConverter(Byte.TYPE, String.class, Byte::parseByte);
        vi.addConverter(Character.TYPE, String.class, (String s) -> s.charAt(0));
        vi.addConverter(Short.TYPE, String.class, Short::parseShort);
        vi.addConverter(Integer.TYPE, String.class, Integer::parseInt);
        vi.addConverter(Long.TYPE, String.class, Long::parseLong);
        vi.addConverter(Double.TYPE, String.class, Double::parseDouble);
        vi.addConverter(Float.TYPE, String.class, Float::parseFloat);
        vi.addConverter(Integer.TYPE, Integer.class, (Integer i) -> (int) i);
        vi.addConverter(Double.TYPE, Double.class, d -> d);
        vi.addConverter(Boolean.TYPE, Boolean.class, b -> b);

        return vi;
    }

    /**
     * Injects the converted version of the given {@code arguments} in the given {@code obj}.
     *
     * @param <T> type safety
     * @param obj a non-null instance of a parameter class (with annotation)
     * @param arguments a non-null string map
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException an access on some reflection methods occurred
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException an converter could not translate the given value in arguments
     * @see Option
     * @see Flag
     */
    public <T> T inject(T obj, ScriptCommandAst arguments)
            throws ConversionException, InjectionReflectionException, NoSpecifiedConverterException,
            ArgumentRequiredException {
        List<ProofScriptArgument> meta = ArgumentsLifter.inferScriptArguments(obj.getClass());

        for (ProofScriptArgument arg : meta) {
            injectIntoField(arg, arguments, obj);
        }

        return obj;
    }

    @SuppressWarnings("unchecked")
    private Map<String, Object> getStringMap(Object obj, ProofScriptArgument vararg)
            throws InjectionReflectionException {
        try {
            Map<String, Object> map = (Map<String, Object>) vararg.getField().get(obj);
            if (map == null) {
                map = new HashMap<>();
                vararg.getField().set(obj, map);
            }
            return map;
        } catch (IllegalAccessException e) {
            throw new InjectionReflectionException(
                "Error on using reflection on class " + obj.getClass(), e);
        }
    }

    private void injectIntoField(ProofScriptArgument meta, ScriptCommandAst args, Object obj)
            throws InjectionReflectionException, ArgumentRequiredException, ConversionException,
            NoSpecifiedConverterException {
        Object val = null;
        if (meta.isPositional()) {
            final var idx = meta.getArgumentPosition();
            if (idx < args.positionalArgs().size()) {
                val = args.positionalArgs().get(idx);
            }
        }

        if (meta.isPositionalVarArgs()) {
            val = args.positionalArgs();
        }

        if (meta.isOptionalVarArgs()) {
            OptionalVarargs ov = Objects.requireNonNull(meta.getOptionalVarArgs());
            var targetType = ov.as();
            Map<String, Object> result = new TreeMap<>();
            for (var entry : args.namedArgs().entrySet()) {
                if (entry.getKey().startsWith(ov.prefix())) {
                    result.put(entry.getKey(),
                        convert(entry.getValue(), targetType));
                }
            }
            val = result;
        }

        if (meta.isOption()) {
            val = args.namedArgs().get(meta.getName());
        }

        if (meta.isFlag()) {
            val = args.namedArgs().get(meta.getName());
            System.out.println("X" + val + "  " + args.namedArgs() + "  " + meta.getName());
            if (val == null) {
                // can also be given w/o colon or equal sign, e.g., "command hide;"
                var stringStream = args.positionalArgs().stream()
                        .map(it -> {
                            try {
                                return convert(it, String.class);
                            } catch (NoSpecifiedConverterException | ConversionException e) {
                                return "";
                            }
                        });
                // val == true iff the name of the flag appear as a positional argument.
                val = stringStream.anyMatch(it -> Objects.equals(it, meta.getName()));
                System.out.println(val);
            }
        }

        try {
            meta.getField().setAccessible(true);
            if (val == null) {
                if (meta.isRequired() && meta.getField().get(obj) == null) {
                    throw new ArgumentRequiredException(String.format(
                        "Argument %s (of type %s) is required, but %s was given. For command class: '%s'",
                        meta.getName(), meta.getField().getType(), null,
                        meta.getField().getDeclaringClass()));
                }
            } else {
                Object value = convert(meta, val);
                meta.getField().set(obj, value);
            }
        } catch (IllegalAccessException e) {
            throw new InjectionReflectionException("Could not inject values via reflection", e);
        }

    }

    private Object convert(ProofScriptArgument meta, Object val)
            throws NoSpecifiedConverterException, ConversionException {
        if (meta.isPositionalVarArgs()) {
            var source = (List<?>) val;
            var seq = new ArrayList<>();
            var targetType = meta.getPositionalVarargs().as();
            for (var o : source) {
                seq.add(convert(o, targetType));
            }
            return seq;
        }

        if (meta.isOptionalVarArgs()) {
            var source = (Map<String, ?>) val;
            var seq = new TreeMap<String, Object>();
            var targetType = meta.getOptionalVarArgs().as();
            for (var o : source.entrySet()) {
                seq.put(o.getKey(), convert(o.getValue(), targetType));
            }
            return seq;
        }

        var targetType = meta.getField().getType();
        return convert(targetType, val);
    }

    @SuppressWarnings("unchecked")
    public <T> T convert(Class<T> targetType, Object val)
            throws NoSpecifiedConverterException, ConversionException {
        var converter = (Converter<Object, Object>) getConverter(targetType, val.getClass());
        if (converter == null) {
            throw new NoSpecifiedConverterException(
                "No converter registered for class: " + targetType + " from " + val.getClass());
        }
        try {
            return (T) converter.convert(val);
        } catch (Exception e) {
            throw new ConversionException(
                String.format("Could not convert value '%s' from type '%s' to type '%s'",
                    val, val.getClass(), targetType),
                e);
        }
    }

    public <T> T convert(Object val, Class<T> type)
            throws NoSpecifiedConverterException, ConversionException {
        @SuppressWarnings("unchecked")
        var converter = (Converter<T, Object>) getConverter(type, val.getClass());

        if (converter == null) {
            throw new NoSpecifiedConverterException(
                "No converter registered for class: " + type + " from " + val.getClass(), null);
        }
        try {
            return converter.convert(val);
        } catch (Exception e) {
            throw new ConversionException(
                String.format("Could not convert value %s (%s) to type %s", val, val.getClass(),
                    type),
                e);
        }
    }

    /**
     * Registers the given converter for the specified class.
     *
     * @param ret a class
     * @param conv a converter for the given class
     * @param <T> an arbitrary type
     */
    public <R, T> void addConverter(Class<R> ret, Class<T> arg, Converter<R, T> conv) {
        converters.put(new ConverterKey<>(ret, arg), conv);
    }

    public <R, T> void addConverter(Converter<R, T> conv) {
        var m = conv.getClass().getMethods()[0];
        converters.put(new ConverterKey<>(m.getReturnType(), m.getParameterTypes()[0]), conv);
    }

    /**
     * Finds a converter for the given class.
     *
     * @param <T> an arbitrary type
     * @param ret a non-null class
     * @param arg
     * @return null or a suitable converter (registered) converter for the requested class.
     */
    @SuppressWarnings("unchecked")
    public <R, T> @Nullable Converter<R, T> getConverter(Class<R> ret, Class<T> arg) {
        if (ret == arg) {
            return (T it) -> (R) it;
        }
        return (Converter<R, T>) converters.get(new ConverterKey<>(ret, arg));
    }

    @Override
    public String toString() {
        return "%s(%s)".formatted(
            getClass().getName(),
            converters.keySet().stream().map(Record::toString).collect(Collectors.joining(",\n")));
    }
}
