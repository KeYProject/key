/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

/**
 * Persists the docking layout (which dockables are open in which {@link DockLocation role}) in a
 * plain {@link Properties} file inside the KeY configuration directory.
 * <p>
 * Counter-part of the Docking Frames {@code layout.xml} persistence of the Swing module
 * {@code key.ui}; the file format is deliberately simple and self-contained. The actual
 * sequence of "which dockable belongs to which role" is the persisted content; divider positions
 * and floating windows are not persisted (yet).
 */
public final class DockLayoutStore {

    /** The name of the properties file inside the config directory. */
    public static final String FILE_NAME = "layout.properties";

    private static final String KEY_PREFIX = "dock.";

    private final Path file;

    /**
     * Creates a store writing to the given config directory.
     *
     * @param configDir the KeY configuration directory
     */
    public DockLayoutStore(Path configDir) {
        this.file = configDir.resolve(FILE_NAME);
    }

    /**
     * @return the properties file backing this store
     */
    public Path file() {
        return file;
    }

    /**
     * Stores the open dockables per role.
     *
     * @param openDockables the ordered dockable ids per role
     * @throws IOException on I/O errors
     */
    public void save(Map<DockLocation, List<String>> openDockables) throws IOException {
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
        Properties properties = new Properties();
        for (DockLocation location : DockLocation.values()) {
            List<String> ids = openDockables.getOrDefault(location, List.of());
            properties.setProperty(KEY_PREFIX + location.name(), String.join(",", ids));
        }
        try (var out = Files.newOutputStream(file)) {
            properties.store(out, "KeY JavaFX UI docking layout");
        }
    }

    /**
     * Loads the stored layout.
     *
     * @return the ordered dockable ids per role; roles absent from the file (or missing file)
     *         yield empty lists
     * @throws IOException on I/O errors
     */
    public Map<DockLocation, List<String>> load() throws IOException {
        EnumMap<DockLocation, List<String>> result = new EnumMap<>(DockLocation.class);
        for (DockLocation location : DockLocation.values()) {
            result.put(location, List.of());
        }
        if (!Files.isRegularFile(file)) {
            return result;
        }
        Properties properties = new Properties();
        try (var in = Files.newInputStream(file)) {
            properties.load(in);
        }
        for (DockLocation location : DockLocation.values()) {
            String value = properties.getProperty(KEY_PREFIX + location.name(), "");
            List<String> ids = Arrays.stream(value.split(",")).map(String::trim)
                    .filter(s -> !s.isEmpty()).toList();
            result.put(location, ids);
        }
        return result;
    }

    /**
     * Deletes the persisted layout, if present.
     *
     * @throws IOException on I/O errors
     */
    public void clear() throws IOException {
        Files.deleteIfExists(file);
    }
}
