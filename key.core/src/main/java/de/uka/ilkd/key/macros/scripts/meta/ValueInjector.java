/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

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
    private static ValueInjector instance;

    /**
     * A mapping between desired types and suitable @{@link StringConverter}.
     * <p>
     * Should be
     *
     * <pre>
     * T --> StringConverter<T>
     * </pre>
     */
    private final Map<Class, StringConverter> converters = new HashMap<>();

    /**
     * Injects the given {@code arguments} in the {@code obj}. For more details see
     * {@link #inject(ProofScriptCommand, Object, Map)}
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
    public static <T> T injection(ProofScriptCommand<T> command, T obj,
            Map<String, String> arguments) throws ArgumentRequiredException,
            InjectionReflectionException, NoSpecifiedConverterException, ConversionException {
        return getInstance().inject(command, obj, arguments);
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
        vi.addConverter(Integer.class, Integer::parseInt);
        vi.addConverter(Long.class, Long::parseLong);
        vi.addConverter(Boolean.class, Boolean::parseBoolean);
        vi.addConverter(Double.class, Double::parseDouble);
        vi.addConverter(String.class, (String s) -> s);
        vi.addConverter(Boolean.TYPE, Boolean::parseBoolean);
        vi.addConverter(Byte.TYPE, Byte::parseByte);
        vi.addConverter(Character.TYPE, s -> s.charAt(0));
        vi.addConverter(Short.TYPE, Short::parseShort);
        vi.addConverter(Integer.TYPE, Integer::parseInt);
        vi.addConverter(Long.TYPE, Long::parseLong);
        vi.addConverter(Double.TYPE, Double::parseDouble);
        vi.addConverter(Float.TYPE, Float::parseFloat);
        return vi;
    }

    /**
     * Injects the converted version of the given {@code arguments} in the given {@code obj}.
     *
     * @param command a proof script command
     * @param obj a non-null instance of a parameter class (with annotation)
     * @param arguments a non-null string map
     * @param <T> type safety
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException an access on some reflection methods occurred
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException an converter could not translate the given value in arguments
     * @see Option
     * @see Flag
     */
    public <T> T inject(ProofScriptCommand<T> command, T obj, Map<String, String> arguments)
            throws ConversionException, InjectionReflectionException, NoSpecifiedConverterException,
            ArgumentRequiredException {
        List<ProofScriptArgument<T>> meta =
            ArgumentsLifter.inferScriptArguments(obj.getClass(), command);
        List<ProofScriptArgument<T>> varArgs = new ArrayList<>(meta.size());

        List<String> usedKeys = new ArrayList<>();

        for (ProofScriptArgument<T> arg : meta) {
            if (arg.hasVariableArguments()) {
                varArgs.add(arg);
            } else {
                injectIntoField(arg, arguments, obj);
                usedKeys.add(arg.getName());
            }
        }

        for (ProofScriptArgument<T> vararg : varArgs) {
            final Map<String, Object> map = getStringMap(obj, vararg);
            final int prefixLength = vararg.getName().length();
            for (Map.Entry<String, String> e : arguments.entrySet()) {
                String k = e.getKey();
                String v = e.getValue();
                if (!usedKeys.contains(k) && k.startsWith(vararg.getName())) {
                    map.put(k.substring(prefixLength), convert(vararg, v));
                    usedKeys.add(k);
                }
            }
        }

        return obj;
    }

    @SuppressWarnings("unchecked")
    private Map<String, Object> getStringMap(Object obj, ProofScriptArgument<?> vararg)
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
                "Error on using reflection on class " + obj.getClass(), e, vararg);
        }
    }

    private void injectIntoField(ProofScriptArgument<?> meta, Map<String, String> args, Object obj)
            throws InjectionReflectionException, ArgumentRequiredException, ConversionException,
            NoSpecifiedConverterException {
        final String val = args.get(meta.getName());
        if (val == null) {
            if (meta.isRequired()) {
                throw new ArgumentRequiredException(String.format(
                    "Argument %s:%s is required, but %s was given. " + "For comamnd class: '%s'",
                    meta.getName(), meta.getField().getType(), val, meta.getCommand().getClass()),
                    meta);
            }
        } else {
            Object value = convert(meta, val);
            try {
                // if (meta.getType() != value.getClass())
                // throw new ConversionException("The typed returned '" + val.getClass()
                // + "' from the converter mismatched with the
                // type of the field " + meta.getType(), meta);
                // FIXME: I had to add this, otherwise I would receive an illegal access exception.
                meta.getField().setAccessible(true);
                meta.getField().set(obj, value);
            } catch (IllegalAccessException e) {
                throw new InjectionReflectionException("Could not inject values via reflection", e,
                    meta);
            }
        }
    }

    private Object convert(ProofScriptArgument<?> meta, String val)
            throws NoSpecifiedConverterException, ConversionException {
        StringConverter<?> converter = getConverter(meta.getType());
        if (converter == null) {
            throw new NoSpecifiedConverterException(
                "No converter registered for class: " + meta.getField().getType(), meta);
        }
        try {
            return converter.convert(val);
        } catch (Exception e) {
            throw new ConversionException(String.format("Could not convert value %s to type %s",
                val, meta.getField().getType().getName()), e, meta);
        }
    }

    /**
     * Registers the given converter for the specified class.
     *
     * @param clazz a class
     * @param conv a converter for the given class
     * @param <T> an arbitrary type
     */
    public <T> void addConverter(Class<T> clazz, StringConverter<T> conv) {
        converters.put(clazz, conv);
    }

    /**
     * Finds a converter for the given class.
     *
     * @param clazz a non-null class
     * @param <T> an arbitrary type
     * @return null or a suitable converter (registered) converter for the requested class.
     */
    @SuppressWarnings("unchecked")
    public <T> StringConverter<T> getConverter(Class<T> clazz) {
        return (StringConverter<T>) converters.get(clazz);
    }
}
