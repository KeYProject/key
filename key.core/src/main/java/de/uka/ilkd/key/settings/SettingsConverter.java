package de.uka.ilkd.key.settings;

import de.uka.ilkd.key.smt.solvertypes.SolverPropertiesLoader;
import org.key_project.util.Streams;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public final class SettingsConverter {
    private static String[][] encoding = { { "#", "#hash" }, // must be the first in the list.
        { "\n", "#newline" }, { "\t", "#tab" }, { "=", "#equals" }, { "\\\"", "#qmark" },
        { "\\\\", "#backslash" }, { ",", "#comma" } };
    private static final String PREFIX = "#beg";
    private static final String POSTFIX = "#end";
    private static final String LIST_SEPARATOR = ",";

    private SettingsConverter() {
    }

    public static String convert(String str, boolean encode) {
        String result = str;
        for (String[] strings : encoding) {
            result = result.replaceAll(strings[encode ? 1 : 0], strings[encode ? 0 : 1]);
        }
        return result;
    }

    public static String encode(String str) {
        int i = str.indexOf(PREFIX);
        if (i == 0) {
            str = str.substring(PREFIX.length());
        } else {
            throw new RuntimeException(
                String.format("Given string '%s' has not the right prefix ('%s').", str, PREFIX));
        }
        i = str.lastIndexOf(POSTFIX);
        str = str.substring(0, i);
        return convert(str, true);
    }

    public static String decode(String str) {
        return PREFIX + convert(str, false) + POSTFIX;
    }


    public static String read(Properties props, String key, String defaultVal) {
        String eth = props.getProperty(key);
        try {
            return eth == null ? defaultVal : encode(eth);
        } catch (Exception e) {
            return defaultVal;
        }
    }

    public static String readRawString(Properties props, String key, String defaultValue) {
        String value = props.getProperty(key);
        if (value == null) {
            value = defaultValue;
        }
        return value;
    }

    public static String[] readRawStringList(Properties props, String key, String split,
            String[] defaultValue) {
        String value = props.getProperty(key);
        if (value == null) {
            return defaultValue;
        }
        return value.split(split);
    }


    public static String readFile(Properties props, String key, String defaultValue) {
        String filePath = props.getProperty(key);
        if (filePath == null) {
            return defaultValue;
        }
        InputStream fileContent = SolverPropertiesLoader.class.getResourceAsStream(filePath);
        if (fileContent == null) {
            return defaultValue;
        }
        try {
            return Streams.toString(fileContent);
        } catch (IOException e) {
            return defaultValue;
        }
    }

    public static int read(Properties props, String key, int defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        try {
            return Integer.parseInt(eth);
        } catch (NumberFormatException e) {
            return defaultVal;
        }

    }

    public static long read(Properties props, String key, long defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        try {
            return Long.parseLong(eth);
        } catch (NumberFormatException e) {
            return defaultVal;
        }
    }

    public static boolean read(Properties props, String key, boolean defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        if (eth.equals("true")) {
            return true;
        }
        if (eth.equals("false")) {
            return false;
        }
        return defaultVal;
    }


    public static String[] read(Properties props, String key, String[] defaultVal) {
        String val = props.getProperty(key);
        if (val == null) {
            return defaultVal;
        }
        String[] result = val.split(LIST_SEPARATOR);
        for (int i = 0; i < result.length; i++) {
            try {
                result[i] = encode(result[i]);
            } catch (Exception e) {
                return defaultVal;
            }
        }
        return result;

    }


    public static void store(Properties props, String key, String[] values) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            result.append(decode(values[i]));
            result.append(i < values.length - 1 ? "," : "");
        }
        props.setProperty(key, result.toString());
    }


    public static void store(Properties props, String key, String value) {
        if (key != null && value != null) {
            props.setProperty(key, decode(value));
        }
    }

    public static void store(Properties props, String key, boolean value) {
        if (key != null) {
            props.setProperty(key, value ? "true" : "false");
        }
    }

    public static void store(Properties props, String key, long value) {
        if (key != null) {
            props.setProperty(key, Long.toString(value));
        }
    }

    public static <T extends Enum<?>> T read(Properties props, String key, T defaultValue,
            T[] values) {
        int ord = read(props, key, defaultValue.ordinal());
        for (T value : values) {
            if (ord == value.ordinal()) {
                return value;
            }
        }
        return defaultValue;
    }

    public static <T extends Enum<?>> void store(Properties props, String key, T value) {
        store(props, key, value.ordinal());
    }
}
