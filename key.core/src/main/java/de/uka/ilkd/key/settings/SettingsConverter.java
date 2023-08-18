/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.Properties;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import org.key_project.util.Streams;

/**
 * Utility class providing various methods to read properties.
 *
 * @author ?
 */
public final class SettingsConverter {

    /**
     * Encodings for properties values.
     * <ul>
     * <li>"#hash" in a props file encodes "#"</li>
     * <li>"#newline" in a props file encodes "\n"</li>
     * </ul>
     * <br>
     *
     * Note that, in order to guarantee dec(enc(*)) = enc(dec(*)) = id(*), care has to be taken:
     * <ol>
     * <li>The replacement order needs to be inverted for dec
     * (see {@link #convert(String, boolean)}).</li>
     * <li>If any of the Strings replaced by dec occurs in str from the beginning, enc(str) has
     * to change these and vice versa. Otherwise, cases like the following will break:
     * dec("=") = "="; enc("=") = "#equals" -> enc(dec("=")) = "#equals" != "="</li>
     * </ol>
     *
     * TODO enc(dec(*)) = id is currently not guaranteed.
     * 2. is only guaranteed by enc because any occurrence of "#..." will be encoded to
     * "#hash...". Thus,
     */
    private static final String[][] ENCODINGS = { { "#", "#hash" }, // has to be first for enc
        { "\n", "#newline" }, { "\t", "#tab" }, { "=", "#equals" }, { "\\\"", "#qmark" },
        { "\\\\", "#backslash" }, { ",", "#comma" } };

    /**
     * Used to mark the beginning of a properties value.
     */
    private static final String PREFIX = "#beg";
    /**
     * Used to mark the end of a properties value.
     */
    private static final String POSTFIX = "#end";

    /**
     * Used to separate values in properties lists.
     */
    private static final String LIST_SEPARATOR = ",";

    /**
     * The class doesn't need to be instantiated as it only contains static methods.
     */
    private SettingsConverter() {}

    /**
     * Replace occurrences of Strings in {@link #ENCODINGS} by their corresponding encoding String.
     *
     * @param str the String to be encoded
     * @return the encoded String
     */
    public static String encodeString(String str) {
        return convert(str, true);
    }

    /**
     * Replace occurrences of Strings in {@link #ENCODINGS} by their corresponding decoding String.
     *
     * @param str the String to be decoded
     * @return the decoded String
     */
    public static String decodeString(String str) {
        return convert(str, false);
    }

    /**
     * Replace occurrences of Strings in {@link #ENCODINGS} by their corresponding encoding/decoding
     * String.
     * <br>
     * The order of the replacements depends on whether the String is encoded or decoded
     * (see {@link #encode(String)} and {@link #decode(String)}).
     * <br>
     * If encode is true: the first element of each row is replaced by the second.
     * If encode is false: the second element of each row is replaced by the first.
     *
     * @param str the String to be encoded/decoded
     * @param encode true if the String should be encoded, false if it should be decoded
     * @return the encoded/decoded String
     */
    private static String convert(String str, boolean encode) {
        String result = str;
        for (int i = 0; i < ENCODINGS.length; i++) {
            // The order of replacements has to be reversed when decoding the String.
            // Previously both enc and dec went through the array from front to back which
            // would, for example, break the following:
            // enc: "#newline" -> "#hashnewline"; dec: "#hashnewline" -> "#newline" -> "\n"
            // -> dec(enc(#newline)) = \n != #newline
            String[] encodingPair = ENCODINGS[encode ? i : (ENCODINGS.length - 1 - i)];
            result = result.replaceAll(
                encodingPair[encode ? 0 : 1],
                encodingPair[encode ? 1 : 0]);
        }
        return result;
    }

    /**
     * Decode the given String according to the following rules:
     * <ul>
     * <li>The String has to start with {@link #PREFIX} and end with {@link #POSTFIX}, otherwise
     * a RuntimeException is thrown.</li>
     * <li>Each occurrence of a String in the 2nd column of {@link #ENCODINGS} is replaced by the
     * corresponding element in the first column of {@link #ENCODINGS}.</li>
     * <li>The Strings in {@link #ENCODINGS} are replaced from back to front,
     * i.e. first each occurrence of "#comma" is replaced by ",",
     * then each "#backslash" by "\\\\" and so on until finally each
     * "#hash" is replaced by "#".</li>
     * </ul>
     *
     * @param str the String to decode
     * @return the decoded version of str
     */
    public static String decode(@Nonnull String str) {
        int i = str.indexOf(PREFIX);
        if (i == 0) {
            str = str.substring(PREFIX.length());
        } else {
            throw new IllegalArgumentException(
                String.format("Given string '%s' doesn't have the right prefix ('%s').",
                    str, PREFIX));
        }
        i = str.lastIndexOf(POSTFIX);
        str = str.substring(0, i);
        return decodeString(str);
    }

    /**
     * Encode a String according to the following rules:
     * <ul>
     * <li>
     * The encoded String is prefixed with {@link #PREFIX} and suffixed with {@link #POSTFIX}.
     * </li>
     * <li>
     * Each occurrence of a String in the 1st column of {@link #ENCODINGS} is replaced by the
     * corresponding element in the first column of {@link #ENCODINGS}.
     * </li>
     * <li>
     * The Strings in {@link #ENCODINGS} are replaced from front to back,
     * i.e. first each occurrence of "#" is replaced by "#hash", then
     * each "\n" is replaced by "#newline" and so on until finally
     * each "," is replaced by "#comma".
     * </li>
     * </ul>
     *
     * @param str the String to encode
     * @return the encoded version of str
     */
    public static String encode(@Nonnull String str) {
        return PREFIX + encodeString(str) + POSTFIX;
    }


    /**
     * Read a String property and replace {@link #ENCODINGS}s by the value they encode
     * (see {@link #decode(String)}.
     *
     * @param props the properties object to be read
     * @param key the properties object's key to be read
     * @param defaultVal the default value to return if the key is not found
     * @return the encoded value of the given key if found, otherwise the given defaultVal
     */
    public static String read(Properties props, String key, String defaultVal) {
        String eth = props.getProperty(key);
        try {
            return eth == null ? defaultVal : decode(eth);
        } catch (Exception e) {
            return defaultVal;
        }
    }

    /**
     * Checks whether the given properties contain a key whose String
     * representation is not contained in the given set of supported keys.
     * The returned list is empty iff all the properties object's
     * keys have String representations in supportedKeys.
     *
     * @param props the properties object whose keys are to check
     * @param supportedKeys the allowed String representations of keys in the given props
     * @return the list of String representations of unsupported keys
     */
    public static Collection<String> unsupportedPropertiesKeys(
            Properties props, String... supportedKeys) {
        return props.keySet().stream().map(Object::toString)
                .filter(k -> !Arrays.asList(supportedKeys).contains(k))
                .collect(Collectors.toList());
    }

    /**
     * Read a raw String property without paying attention to {@link #ENCODINGS}s.
     * The read value will thus be returned without any changes.
     *
     * @param props the properties object to be read
     * @param key the properties object's key to be read
     * @param defaultValue the default value to return if the key is not found
     * @return the read String value
     */
    public static String readRawString(Properties props, String key, String defaultValue) {
        String value = props.getProperty(key);
        if (value == null) {
            value = defaultValue;
        }
        return value;
    }

    /**
     * Read a list of raw Strings (see {@link #readRawString(Properties, String, String)}).
     *
     * @param props the properties object to be read
     * @param key the properties object's key to be read
     * @param split the String used for splitting the list values
     * @param defaultValue the default value to return if the key is not found
     * @return the given key's value split into a list at occurrences of split
     */
    public static String[] readRawStringList(Properties props, String key, String split,
            String[] defaultValue) {
        String value = props.getProperty(key);
        if (value == null) {
            return defaultValue;
        }
        return value.split(split);
    }

    /**
     * Read a file path from a file path in the properties object.
     * If the key is not found, the default value will be returned.
     * Otherwise, the value is interpreted as a file path and the corresponding file
     * is searched using the given class loader. If the file is found, it's content
     * is returned as a String.
     * If something goes wrong (e.g. file is not found, file cannot be read),
     * the default value is returned.
     *
     * @param props the properties object to read
     * @param key the key whose value is to be read as an int
     * @param defaultVal the default value to read if the key isn't found or the corresponding
     *        file cannot be found/read
     * @param loader the ClassLoader to use for searching the file
     * @return the read file content
     */
    public static String readFile(Properties props, String key, String defaultVal,
            ClassLoader loader) {
        String filePath = props.getProperty(key);
        if (filePath == null) {
            return defaultVal;
        }
        InputStream fileContent = loader.getResourceAsStream(filePath);
        if (fileContent == null) {
            return defaultVal;
        }
        try {
            return Streams.toString(fileContent);
        } catch (IOException e) {
            return defaultVal;
        }
    }

    /**
     * Read an integer value. If the key's value cannot be parsed into int, the default value
     * will be returned.
     *
     * @param props the properties object to read
     * @param key the key whose value is to be read as an int
     * @param defaultVal the default value to read if the key isn't found or cannot
     *        be parsed into int
     * @return the read int value
     */
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

    /**
     * Read a long value. If the key's value cannot be parsed into long, the default value
     * will be returned.
     *
     * @param props the properties object to read
     * @param key the key whose value is to be read as a long
     * @param defaultVal the default value to read if the key isn't found or cannot
     *        be parsed into long
     * @return the read long value
     */
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

    /**
     * Read a boolean. If the value is "false", return false. If the value is "true", return true.
     * Otherwise, return the default value. Note that this is case-sensitive (e.g. "FALSE" and
     * "True" lead to the default value being returned).
     *
     * @param props the properties object to read
     * @param key the key whose value is to be read as a boolean.
     *        The value has to be one of "true", "false" (case-sensitive).
     * @param defaultVal the default value to read if the key is not found or doesn't
     *        equal "true" or "false"
     * @return true iff the read value is "true", false iff the read value is "false",
     *         defaultVal otherwise
     */
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

    /**
     * Read a String list. The elements are assumed to be separated by {@link #LIST_SEPARATOR}.
     * The read Strings are encoded using {@link #decode(String)}.
     *
     * @param props the properties object to read
     * @param key the key whose value is to be read as a String list
     * @param defaultVal the default list to read if the key is not found
     * @return the read String list with separately encoded elements
     */
    public static String[] read(Properties props, String key, String[] defaultVal) {
        String val = props.getProperty(key);
        if (val == null) {
            return defaultVal;
        }
        String[] result = val.split(LIST_SEPARATOR);
        for (int i = 0; i < result.length; i++) {
            try {
                result[i] = decode(result[i]);
            } catch (Exception e) {
                return defaultVal;
            }
        }
        return result;

    }

    /**
     * Store a String list. The list elements are separated using {@link #LIST_SEPARATOR}.
     *
     * @param props the properties object to write
     * @param key the key whose value is to be stored
     * @param values the array to store as a list
     */
    public static void store(Properties props, String key, String[] values) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            result.append(encode(values[i]));
            result.append(i < values.length - 1 ? LIST_SEPARATOR : "");
        }
        props.setProperty(key, result.toString());
    }

    /**
     * Store a String value after decoding it with {@link #encode(String)}.
     *
     * @param props the properties object to write
     * @param key the key whose value is to be stored
     * @param value the String value to store for key
     */
    public static void store(Properties props, String key, String value) {
        if (key != null && value != null) {
            props.setProperty(key, encode(value));
        }
    }

    /**
     * Store a boolean value.
     *
     * @param props the properties object to write
     * @param key the key whose value is to be stored
     * @param value the boolean value to store for key
     */
    public static void store(Properties props, String key, boolean value) {
        if (key != null) {
            props.setProperty(key, value ? "true" : "false");
        }
    }

    /**
     * Store a long value.
     *
     * @param props the properties object to write
     * @param key the key whose value is to be stored
     * @param value the long value to store for key
     */
    public static void store(Properties props, String key, long value) {
        if (key != null) {
            props.setProperty(key, Long.toString(value));
        }
    }

    /**
     * Read an enum constant property by its ordinal.
     *
     * @param props the properties object to read
     * @param key the key whose value is the enum constant's ordinal in enum T
     * @param defaultValue the default enum constant of T to return
     * @param values the enum values of T from which to choose the value to read
     * @return the value of the read enum constant
     * @param <T> the enum which the read constant belongs to
     */
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

    /**
     * Store an enum constant via its ordinal.
     *
     * @param props the properties object to write
     * @param key the key whose value is the enum constant's ordinal
     * @param value the enum constant of enum T which is to store
     * @param <T> the enum which the stored constant belongs to
     */
    public static <T extends Enum<?>> void store(Properties props, String key, T value) {
        store(props, key, value.ordinal());
    }
}
