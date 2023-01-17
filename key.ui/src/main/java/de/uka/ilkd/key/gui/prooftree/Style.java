package de.uka.ilkd.key.gui.prooftree;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import java.awt.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Style {
    private final Map<Object, Object> styles = new HashMap<>();
    private final Set<Object> sealed = new HashSet<>();

    private static class Key<T> {
        <T> Key(Class<T> clazz) {
        }
    }

    public static final Key<Color> KEY_COLOR_FOREGROUND = new Key<>(Color.class);
    public static final Key<Color> KEY_COLOR_BACKGROUND = new Key<>(Color.class);
    public static final Key<Color> KEY_COLOR_BORDER = new Key<>(Color.class);
    public static final Key<Boolean> KEY_FONT_ITALIC = new Key<>(Boolean.class);
    public static final Key<Boolean> KEY_FONT_BOLD = new Key<>(Boolean.class);
    public static final Key<Icon> KEY_ICON = new Key<>(Icon.class);
    public static final Key<String> KEY_TOOLTIP = new Key<>(String.class);
    public static final Key<String> KEY_TEXT = new Key<>(String.class);

    @Nonnull
    public <T> Style set(@Nonnull Key<T> key, @Nullable T value) {
        if (!sealed.contains(key)) {
            styles.put(key, value);
        }
        return this;
    }

    @Nonnull
    public <T> Style setAndSeal(@Nonnull Key<T> key, @Nullable T value) {
        set(key, value);
        sealed.add(key);
        return this;
    }

    public <T> boolean contains(@Nonnull Key<T> key) {
        return styles.containsKey(key);
    }

    @Nullable
    @SuppressWarnings("unchecked")
    public <T> T get(@Nonnull Key<T> key, @Nullable T defaultValue) {
        return (T) styles.getOrDefault(key, defaultValue);
    }

    @Nullable
    public <T> T get(@Nonnull Key<T> key) {
        return get(key, null);
    }

    public boolean getBoolean(Key<Boolean> key) {
        return get(key) == Boolean.TRUE;
    }
}
