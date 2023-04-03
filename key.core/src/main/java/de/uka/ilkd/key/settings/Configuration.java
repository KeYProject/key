package de.uka.ilkd.key.settings;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.util.Position;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.*;

/**
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

    public static Configuration load(File file) throws IOException {
        return ParsingFacade.readConfigurationFile(file);
    }

    public boolean exists(String name) {
        return data.containsKey(name);
    }

    public <T> boolean exists(String name, Class<T> clazz) {
        return data.containsKey(name) && clazz.isAssignableFrom(data.get(name).getClass());
    }

    public <T> T get(String name, Class<T> clazz) {
        if (exists(name, clazz)) return (T) data.get(name);
        else return null;
    }

    @Nonnull
    public <T> T get(String name, @Nonnull T defaultValue) {
        if (exists(name, defaultValue.getClass())) return (T) data.get(name);
        else return defaultValue;
    }

    @Nullable
    public Object get(String name) {
        return data.get(name);
    }

    public int getInt(String name) {
        return get(name, Integer.class);
    }

    public int getInt(String name, int defaultValue) {
        return get(name, defaultValue);
    }

    public long getLong(String name) {
        return get(name, Integer.class);
    }

    public long getLong(String name, long defaultValue) {
        return getInt(name, (int) defaultValue);
    }


    public boolean getBool(String name) {
        return get(name, Boolean.class);
    }

    public boolean getBool(String name, boolean defaultValue) {
        return get(name, defaultValue);
    }

    public double getDouble(String name) {
        return get(name, Double.class);
    }

    public String getString(String name) {
        return get(name, String.class);
    }

    public String getString(String name, String defaultValue) {
        return get(name, defaultValue);
    }

    public Configuration getTable(String name) {
        return get(name, Configuration.class);
    }

    public List<Object> getList(String name) {
        return get(name, List.class);
    }

    public List<String> getStringList(String name) {
        var seq = get(name, List.class);
        if (!seq.stream().allMatch(it -> it instanceof String)) throw new AssertionError();
        return seq;
    }

    @Nonnull
    public String[] getStringArray(String name, @Nonnull String[] defaultValue) {
        if (exists(name)) {
            return getStringList(name).toArray(new String[0]);
        } else return defaultValue;
    }


    @Nullable
    public ConfigurationMeta getMeta(String name) {
        return meta.get(name);
    }

    @Nonnull
    private ConfigurationMeta getOrCreateMeta(String name) {
        return Objects.requireNonNull(meta.putIfAbsent(name, new ConfigurationMeta()));
    }


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

    public Set<Map.Entry<String, Object>> getEntries() {
        return data.entrySet();
    }

    public <T extends Enum<T>> T getEnum(String name, T defaultValue) {
        var idx = getString(name);
        try {
            return Enum.valueOf((Class<T>) defaultValue.getClass(), idx);
        } catch (IllegalArgumentException | NullPointerException e) {
            return defaultValue;
        }
    }

    public void save(Writer writer, String comment) {
        new ConfigurationWriter(writer).printComment(comment).printConfiguration(this);
    }


    public static class ConfigurationMeta {
        private Position position;

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

    private static class ConfigurationWriter {
        private final PrintWriter out;
        private int indent;
        private int equalSignPos;

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

        public ConfigurationWriter printConfiguration(Configuration c) {
            return printConfiguration(c, true);
        }

        public ConfigurationWriter printConfiguration(Configuration c, boolean section) {
            c.data.forEach((k, v) -> {
                if (v != null) {
                    if (section && v instanceof Configuration)
                        printSection(k, (Configuration) v);
                    else
                        printKeyValue(k, v).newline().reset();
                }
            });
            return this;
        }

        private void printSection(String k, Configuration v) {
            reset();
            out.format("\n[%s]\n", k);
            printConfiguration(v, false);
        }

        private ConfigurationWriter reset() {
            equalSignPos = 0;
            return this;
        }

        private ConfigurationWriter printKeyValue(String key, Object value) {
            return printKey(key).printValue(value);
        }

        private ConfigurationWriter newline() {
            out.println();
            return this;
        }

        private ConfigurationWriter printValue(Object value) {
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
            var old = equalSignPos;
            var own = equalSignPos += 2;
            out.format("{ ");
            for (Iterator<Map.Entry<String, Object>> iterator = value.entrySet().iterator(); iterator.hasNext(); ) {
                Map.Entry<String, Object> entry = iterator.next();
                String k = entry.getKey();
                Object v = entry.getValue();
                printKeyValue(k, v);
                if (iterator.hasNext()) {
                    print(",").newline();
                    equalSignPos = own;
                    fillSpaces();
                }
            }
            out.format(" }");
            equalSignPos = old;
            return this;
        }

        private void fillSpaces() {
            for (int i = 0; i < equalSignPos; i++) {
                print(" ");
            }
        }

        private ConfigurationWriter print(String s) {
            out.print(s);
            return this;
        }

        private ConfigurationWriter printSeq(Collection<Object> value) {
            var old = equalSignPos;
            equalSignPos += 2;
            out.format("[ ");
            for (Iterator<Object> iterator = value.iterator(); iterator.hasNext(); ) {
                Object o = iterator.next();
                printValue(o);
                if (iterator.hasNext()) {
                    if (value.size() <= 5) {
                        print(", ");
                    } else {
                        print(",");
                        newline();
                        fillSpaces();
                    }
                }
            }
            out.format(" ]");
            equalSignPos = old;
            return this;
        }

        private ConfigurationWriter printKey(String key) {
            if (key.contains(" ") || key.contains("(") || key.contains(")") || key.contains("[s")) {
                printValue(key);
                equalSignPos += key.length() + 5;
            } else {
                out.write(key);
                equalSignPos += key.length() + 3;
            }
            out.format(" = ");
            return this;
        }
    }
}
