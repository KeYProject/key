/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.*;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.util.Position;

import org.antlr.v4.runtime.CharStream;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


/**
 * A container to hold parsed configurations. Configurations are a mapping between property names
 * and values plus additional meta-information (line number, documentation, etc.).
 * <p>
 * Helper functions allow to access the values in a type-safe fashion.
 * Note that configurations may also be nested, use {@link #getTable(String)} to receive a sub
 * configuration.
 *
 * @author Alexander Weigl
 * @version 1 (03.04.23)
 */
public class Configuration {
    private final Map<String, Object> data;
    private final Map<String, ConfigurationMeta> meta = new HashMap<>();

    public Configuration() {
        this(new TreeMap<>());
    }

    public Configuration(Map<String, Object> data) {
        this.data = data;
    }

    /**
     * Loads a configuration using the given file.
     *
     * @param file existsing file path
     * @return a configuration based on the file contents
     * @throws IOException if file does not exists or i/o error
     */
    public static Configuration load(File file) throws IOException {
        return ParsingFacade.readConfigurationFile(file);
    }

    /**
     * Loads a configuration using the given char stream.
     *
     * @param input existing file path
     * @return a configuration based on the file contents
     * @throws IOException i/o error on the steram
     */
    public static Configuration load(CharStream input) throws IOException {
        return ParsingFacade.readConfigurationFile(input);
    }

    /**
     * Returns true if an entry for the given name exists.
     */
    public boolean exists(String name) {
        return data.containsKey(name);
    }

    /**
     * Returns true if an entry for the given name exists and is also compatible
     * with the given class.
     *
     * @see #getBool(String)
     * @see #getInt(String)
     * @see #getLong(String)
     * @see #getDouble(String)
     * @see #getTable(String)
     */
    public <T> boolean exists(String name, Class<T> clazz) {
        return data.containsKey(name) && clazz.isAssignableFrom(data.get(name).getClass());
    }

    /**
     * Returns the stored value for the given name casted to the given clazz if possible.
     * If no value exists, or value is not compatible to {@code clazz}, {@code null} is returned.
     *
     * @param <T> an arbitrary class, exptected return type
     * @param name property name
     * @param clazz data type because of missing reified generics.
     */
    public <T> @Nullable T get(String name, Class<T> clazz) {
        if (exists(name, clazz))
            return clazz.cast(data.get(name));
        else
            return null;
    }

    /**
     * The same as {@link #get(String, Class)} but returns the {@code defaultValue} instead
     * of a {@code null} reference.
     *
     * @param <T> the expected return type compatible to the {@code defaultValue}
     * @param name property name
     * @param defaultValue the returned instead of {@code null}.
     */

    public <T> @NonNull T get(String name, Class<T> clazz, @NonNull T defaultValue) {
        if (exists(name, defaultValue.getClass()))
            return clazz.cast(data.get(name));
        else
            return defaultValue;
    }

    /**
     * Get the value for the entry named {@code name}. Null if no such entry exists.
     *
     * @see #exists(String)
     */

    public @Nullable Object get(String name) {
        return data.get(name);
    }

    /**
     * Returns an integer from the configuration.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link java.lang.Long}
     * @throws NullPointerException if no such value entry exists
     */
    public int getInt(String name) {
        return (int) getLong(name);
    }

    /**
     * Returns an integer value for the given name.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Long}
     * @throws NullPointerException if no such value entry exists
     */
    public int getInt(String name, int defaultValue) {
        return (int) getLong(name, defaultValue);
    }

    /**
     * Returns a long value for the given name.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Long}
     * @throws NullPointerException if no such value entry exists
     */
    public long getLong(String name) {
        return get(name, Long.class);
    }

    /**
     * Returns a long value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Long}
     */
    public long getLong(String name, long defaultValue) {
        Long value = get(name, Long.class);
        return Objects.requireNonNullElse(value, defaultValue);
    }

    /**
     * Returns a boolean value for the given name.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Boolean}
     * @throws NullPointerException if no such value entry exists
     */
    public boolean getBool(String name) {
        return get(name, Boolean.class);
    }

    /**
     * Returns a boolean value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Boolean}
     */
    public boolean getBool(String name, boolean defaultValue) {
        return get(name, Boolean.class, defaultValue);
    }

    /**
     * Returns a double value for the given name. {@code defaultValue} if no such value is
     * present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not an {@link Double}
     * @throws NullPointerException if no such value entry exists
     */
    public double getDouble(String name) {
        return get(name, Double.class);
    }

    /**
     * Returns a string value for the given name.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link String}
     */
    @Nullable
    public String getString(String name) {
        return get(name, String.class);
    }

    /**
     * Returns a string value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not an {@link String}
     */
    public String getString(String name, String defaultValue) {
        return get(name, String.class, defaultValue);
    }

    /**
     * Returns a sub configuration for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link Configuration}
     */
    @Nullable
    public Configuration getTable(String name) {
        return get(name, Configuration.class);
    }

    /**
     * Returns a list of objects for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     * @throws ClassCastException if the entry is not a {@link List}
     */
    @Nullable
    public List<Object> getList(String name) {
        return getList(name, Object.class);
    }

    /**
     * Returns a list of elements for the given name.
     * The class type for the elements is given by the {@code clazz} parameter.
     * {@code null} if no such value is present.
     *
     * @param name property name
     * @param clazz the class type of the elements
     * @throws ClassCastException if the entry is not a {@link List} or contains elements of the
     *         wrong type
     */
    @SuppressWarnings("unchecked")
    public <T> @Nullable List<T> getList(String name, Class<T> clazz) {
        List<?> result = get(name, List.class);
        if (result == null) {
            return null;
        }
        if (!result.stream().allMatch(clazz::isInstance)) {
            throw new ClassCastException();
        }
        return (List<T>) result;
    }

    /**
     * Returns a list of strings for the given name.
     *
     * In contrast to the other methods, this method does not throw an exception if the entry does
     * not
     * exist in the configuration. Instead, it returns an empty list.
     *
     * @param name property name
     * @throws ClassCastException if the list contains non-strings
     */
    @SuppressWarnings("unchecked")
    public @NonNull List<String> getStringList(String name) {
        List<?> result = get(name, List.class);
        if (result == null) {
            return Collections.emptyList();
        }
        if (!result.stream().allMatch(String.class::isInstance)) {
            throw new ClassCastException();
        }
        return (List<String>) result;
    }

    /**
     * Returns string array for the requested entry. {@code defaultValue} is returned if no such
     * entry exists.
     *
     * @param name a string identifying the entry
     * @param defaultValue a default value
     * @throws ClassCastException if the given entry has non-string elements
     */
    @NonNull
    public String[] getStringArray(String name, @NonNull String[] defaultValue) {
        if (exists(name)) {
            return getStringList(name).toArray(String[]::new);
        } else
            return defaultValue;
    }

    /**
     * Interprets the given entry as an enum value.
     *
     * @param <T> the enum
     * @param name a name identifying an entry
     * @param defaultValue the default value to be returned
     * @throws ClassCastException if the given entry is not a string
     * @throws IllegalArgumentException if defaultValue does not belong to an enum
     */
    @SuppressWarnings("unchecked")
    public <T extends Enum<T>> @NonNull T getEnum(String name, @NonNull T defaultValue) {
        Class<T> clazz = (Class<T>) defaultValue.getClass();
        if (!clazz.isEnum()) {
            throw new IllegalArgumentException(clazz + " is not an enum type.");
        }
        var idx = getString(name);
        if (idx == null) {
            return defaultValue;
        }

        try {
            return Enum.valueOf(clazz, idx);
        } catch (IllegalArgumentException | NullPointerException e) {
            return defaultValue;
        }
    }

    /**
     * Returns the meta data corresponding to the given entry.
     */
    @Nullable
    public ConfigurationMeta getMeta(String name) {
        return meta.get(name);
    }

    /**
     * Returns the meta data corresponding to the given entry, creates the entry if not existing.
     */
    @NonNull
    private ConfigurationMeta getOrCreateMeta(String name) {
        return Objects.requireNonNull(meta.putIfAbsent(name, new ConfigurationMeta()));
    }

    /**
     * @see #getTable(String)
     */
    public Configuration getSection(String name) {
        return getTable(name);
    }

    public Configuration getOrCreateSection(String name) {
        return getSection(name, true);
    }

    public Configuration getSection(String name, boolean createIfNotExists) {
        if (!exists(name) && createIfNotExists) {
            set(name, new Configuration());
        }
        return getSection(name);
    }

    public Object set(String name, Object obj) {
        return data.put(name, obj);
    }

    public Object set(String name, Boolean obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, String obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, Long obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, int obj) {
        return set(name, (long) obj);
    }

    public Object set(String name, Double obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, Configuration obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, List<?> obj) {
        return set(name, (Object) obj);
    }

    public Object set(String name, String[] seq) {
        return set(name, (Object) Arrays.asList(seq));
    }

    public Set<Map.Entry<String, Object>> getEntries() {
        return data.entrySet();
    }

    /**
     * Serializes this configuration instance into the given writer.
     *
     * @param writer a writer
     * @param comment a comment
     */
    public void save(Writer writer, String comment) {
        new ConfigurationWriter(writer).printComment(comment).printMap(this.data);
    }

    public void overwriteWith(Configuration other) {
        data.putAll(other.data);
    }

    // TODO Add documentation for this.
    /**
     * POJO for metadata of configuration entries.
     */
    public static class ConfigurationMeta {
        /** Position of declaration within a file */
        private Position position;

        /** documentation given in the file */
        private String documentation;

        public Position getPosition() {
            return position;
        }

        public void setPosition(Position position) {
            this.position = position;
        }

        public String getDocumentation() {
            return documentation;
        }

        public void setDocumentation(String documentation) {
            this.documentation = documentation;
        }
    }

    /**
     * Writer for configurations. Mainly manages the indentation levels and escapings.
     */
    public static class ConfigurationWriter {
        private final PrintWriter out;
        private int indent;

        public ConfigurationWriter(Writer writer) {
            this.out = new PrintWriter(writer);
        }

        public ConfigurationWriter printIndent() {
            for (int i = 0; i < indent; i++) {
                out.format(" ");
            }
            return this;
        }

        public ConfigurationWriter printComment(String comment) {
            if (comment.contains("\n")) {
                out.format("/* %s */\n", comment);
            } else {
                out.format("// %s\n", comment);
            }
            return this;
        }

        private ConfigurationWriter printKeyValue(String key, Object value) {
            return printKey(key).printValue(value);
        }

        private ConfigurationWriter newline() {
            out.println();
            return this;
        }

        public ConfigurationWriter printValue(Object value) {
            if (value instanceof String) {
                // TODO What about '"' inside value?
                out.format("\"%s\"", value);
            } else if (value instanceof Long || value instanceof Integer
                    || value instanceof Double || value instanceof Float
                    || value instanceof Short || value instanceof Byte
                    || value instanceof Boolean) {
                out.write(value.toString());
            } else if (value instanceof Collection) {
                printSeq((Collection<?>) value);
            } else if (value instanceof Map) {
                printMap((Map<?, ?>) value);
            } else if (value instanceof Configuration) {
                printMap(((Configuration) value).data);
            } else if (value instanceof Enum<?>) {
                printValue(value.toString());
            } else if (value == null) {
                printValue("null");
            } else {
                throw new IllegalArgumentException("Unexpected object: " + value);
            }
            return this;
        }

        private ConfigurationWriter printMap(Map<?, ?> value) {
            out.format("{ ");
            indent += 4;
            newline().printIndent();
            for (Iterator<? extends Map.Entry<?, ?>> iterator =
                value.entrySet().iterator(); iterator.hasNext();) {
                Map.Entry<?, ?> entry = iterator.next();
                String k = entry.getKey().toString();
                Object v = entry.getValue();
                printKeyValue(k, v);
                if (iterator.hasNext()) {
                    print(",").newline();
                    printIndent();
                }
            }
            indent -= 4;
            newline().printIndent();
            out.format(" }");
            return this;
        }


        private ConfigurationWriter print(String s) {
            out.print(s);
            return this;
        }

        private ConfigurationWriter printSeq(Collection<?> value) {
            out.format("[ ");
            indent += 4;
            newline();
            printIndent();
            for (Iterator<?> iterator = value.iterator(); iterator.hasNext();) {
                Object o = iterator.next();
                printValue(o);
                if (iterator.hasNext()) {
                    if (value.size() <= 5) {
                        print(", ");
                    } else {
                        print(",");
                        newline();
                        printIndent();
                    }
                }
            }
            indent -= 4;
            newline().printIndent();
            out.format(" ]");
            return this;
        }

        private ConfigurationWriter printKey(String key) {
            printValue(key);
            out.format(" : ");
            return this;
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Configuration that))
            return false;
        return Objects.equals(data, that.data);
    }

    @Override
    public int hashCode() {
        return Objects.hash(data);
    }
}
