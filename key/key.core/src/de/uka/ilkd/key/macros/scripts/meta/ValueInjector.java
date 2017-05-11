package de.uka.ilkd.key.macros.scripts.meta;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (29.03.17)
 */
public class ValueInjector {
    private Map<Class, Converter> converters = new HashMap<>();
    private static ValueInjector INSTANCE;

    public <T> T inject(T obj, Map<String, String> arguments)
            throws IllegalAccessException, ConversionException, InjectionReflectionException, NoSpecifiedConverter,
            ArgumentRequiredException {
        List<ProofScriptArgument> meta = ArgumentsLifter.inferScriptArguments(obj.getClass());
        List<ProofScriptArgument> varArgs = new ArrayList<>(meta.size());

        List<String> usedKeys = new ArrayList<>();

        for (ProofScriptArgument arg : meta) {
            if (arg.hasVariableArguments()) {
                varArgs.add(arg);
            }
            else {
                injectIntoField(arg, arguments, obj);
                usedKeys.add(arg.getName());
            }
        }

        for (ProofScriptArgument vararg : varArgs) {
            final Map map = getStringMap(obj, vararg);
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

    private Map getStringMap(Object obj, ProofScriptArgument vararg) throws IllegalAccessException {
        Map map = (Map) vararg.getField().get(obj);
        if (map == null) {
            map = new HashMap();
            vararg.getField().set(obj,map);
        }
        return map;
    }

    private void injectIntoField(ProofScriptArgument meta, Map<String, String> args, Object obj)
            throws InjectionReflectionException, ArgumentRequiredException, ConversionException, NoSpecifiedConverter {
        final String val = args.get(meta.getName());
        if (val == null) {
            if (meta.isRequired())
                throw new ArgumentRequiredException(
                        String.format("Argument %s:%s is required, but %s was given.", meta.getName(),
                                meta.getField().getType(), val), meta);
        }
        else {
            Object value = convert(meta, val);
            try {
                //if (meta.getType() != value.getClass())
                //    throw new ConversionException("The typed returned '" + val.getClass()
                //            + "' from the converter mismtached with the type of the field " + meta.getType(), meta);
                meta.getField().set(obj, value);
            }
            catch (IllegalAccessException e) {
                throw new InjectionReflectionException("Could not inject values via reflection", e, meta);
            }
        }
    }

    @SuppressWarnings("unchecked") private Object convert(ProofScriptArgument meta, String val)
            throws NoSpecifiedConverter, ConversionException {
        Converter converter = getConverter(meta.getType());
        if (converter == null)
            throw new NoSpecifiedConverter("No converter registered for class: " + meta.getField().getType(), meta);

        try {
            return converter.convert(val);
        }
        catch (Exception e) {
            throw new ConversionException(
                    String.format("Could not convert value %s to type %s", val, meta.getField().getType()), e, meta);
        }
    }

    public static <T> T injection(T obj, Map<String, String> arguments)
            throws ArgumentRequiredException, InjectionReflectionException, NoSpecifiedConverter, ConversionException,
            IllegalAccessException {
        return getInstance().inject(obj, arguments);
    }

    public static ValueInjector getInstance() {
        if (INSTANCE == null)
            INSTANCE = createDefault();
        return INSTANCE;
    }

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

    public <T> void addConverter(Class<T> clazz, Converter<T> conv) {
        converters.put(clazz, conv);
    }

    @SuppressWarnings("unchecked") public <T> Converter<T> getConverter(Class<T> clazz) {
        return (Converter<T>) converters.get(clazz);
    }
}
