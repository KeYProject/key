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
 * A container to hold parsed configurations. Configurations are a mapping between a property name
 * and a value plus additional meta information (line number, documentation etc.).
 * <p>
 * Helper functions allow to accesss the values in a type safe fashion.
 * Note that configuration are also nested, use {@link #getTable(String)} to receive a sub
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
     * @param file existsing file path
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
    @Nullable
    public <T> T get(String name, Class<T> clazz) {
        if (exists(name, clazz))
            return (T) data.get(name);
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
    @NonNull
    public <T> T get(String name, @NonNull T defaultValue) {
        if (exists(name, defaultValue.getClass()))
            return (T) data.get(name);
        else
            return defaultValue;
    }

    /**
     * Get the value for the entry named {@code name}. Null if no such entry exists.
     *
     * @see #exists(String)
     */
    @Nullable
    public Object get(String name) {
        return data.get(name);
    }

    /**
     * Returns an integer or {@code null} if not such entry exists.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public int getInt(String name) {
        return (int) getLong(name);
    }

    /**
     * Returns an integer value for the given name. {@code defaultValue} if no such value is
     * present.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public int getInt(String name, int defaultValue) {
        return (int) getLong(name, defaultValue);
    }

    /**
     * Returns a long value for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public long getLong(String name) {
        return get(name, Long.class);
    }

    /**
     * Returns a long value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public long getLong(String name, long defaultValue) {
        var value = get(name, Long.class);
        return Objects.requireNonNullElse(value, defaultValue);
    }

    /**
     * Returns a boolean value for the given name.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public boolean getBool(String name) {
        return get(name, Boolean.class);
    }

    /**
     * Returns a boolean value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public boolean getBool(String name, boolean defaultValue) {
        return get(name, defaultValue);
    }

    /**
     * Returns an integer value for the given name. {@code defaultValue} if no such value is
     * present.
     *
     * @param name property name
     * @throw ClassCastException if the entry is not an {@link #Long}
     * @throw NullPointerException if no such value entry exists
     */
    public double getDouble(String name) {
        return get(name, Double.class);
    }

    /**
     * Returns an string value for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     */
    @Nullable
    public String getString(String name) {
        return get(name, String.class);
    }

    /**
     * Returns an string value for the given name. {@code defaultValue} if no such value is present.
     *
     * @param name property name
     */
    public String getString(String name, String defaultValue) {
        return get(name, defaultValue);
    }

    /**
     * Returns an sub configuration for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     */
    @Nullable
    public Configuration getTable(String name) {
        return get(name, Configuration.class);
    }

    /**
     * Returns a list of objects for the given name. {@code null} if no such value is present.
     *
     * @param name property name
     */
    @Nullable
    public List<Object> getList(String name) {
        return get(name, List.class);
    }

    /**
     * Returns a list of strings for the given name.
     *
     * @param name property name
     * @throws ClassCastException if the list contains non-strings
     */
    @NonNull
    public List<String> getStringList(String name) {
        var seq = get(name, List.class);
        if (seq == null)
            return Collections.emptyList();
        if (!seq.stream().allMatch(it -> it instanceof String))
            throw new ClassCastException();
        return seq;
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
            return getStringList(name).toArray(new String[0]);
        } else
            return defaultValue;
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
        return get(name, Configuration.class);
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
     * Interprets the given entry as an enum value.
     *
     * @param <T> the enum
     * @param name a name identifying an entry
     * @param defaultValue the default value to be returned
     */
    public <T extends Enum<T>> T getEnum(String name, T defaultValue) {
        var idx = getString(name);
        try {
            return Enum.valueOf((Class<T>) defaultValue.getClass(), idx);
        } catch (IllegalArgumentException | NullPointerException e) {
            return defaultValue;
        }
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
     * Writer for configurations. Mainly manages the identation levels and escapings.
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
                out.format("\"%s\"", value);
            } else if (value instanceof Long || value instanceof Integer
                    || value instanceof Double || value instanceof Float
                    || value instanceof Short || value instanceof Byte
                    || value instanceof Boolean) {
                out.write(value.toString());
            } else if (value instanceof Collection) {
                printSeq((Collection<Object>) value);
            } else if (value instanceof Map) {
                printMap((Map<String, Object>) value);
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

        private ConfigurationWriter printMap(Map<String, Object> value) {
            out.format("{ ");
            indent += 4;
            newline().printIndent();
            for (Iterator<Map.Entry<String, Object>> iterator =
                value.entrySet().iterator(); iterator.hasNext();) {
                Map.Entry<String, Object> entry = iterator.next();
                String k = entry.getKey();
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

        private ConfigurationWriter printSeq(Collection<Object> value) {
            out.format("[ ");
            indent += 4;
            newline();
            printIndent();
            for (Iterator<Object> iterator = value.iterator(); iterator.hasNext();) {
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
