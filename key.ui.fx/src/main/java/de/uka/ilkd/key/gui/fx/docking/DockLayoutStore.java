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
import java.util.Optional;
import java.util.Properties;

/**
 * Persists the docking layout (which dockables are open in which {@link DockLocation role}) in a
 * plain {@link Properties} file inside the KeY configuration directory.
 * <p>
 * Counter-part of the Docking Frames {@code layout.xml} persistence of the Swing module
 * {@code key.ui}; the file format is deliberately simple and self-contained. The actual
 * sequence of "which dockable belongs to which role" is the persisted content; divider positions
 * and floating windows are not persisted (yet).
 * <p>
 * Beyond the plain (last-state) layout the store keeps <em>named layout slots</em> — the counter
 * part of the Swing {@code DockingLayout} arrangements {@code Default}/{@code Slot 1}/{@code
 * Slot 2}, which the user fills via {@code View > Layout > Save ...} (Swing {@code
 * SaveLayoutAction}: {@code CControl.save(layoutName)}) and recalls via {@code Load ...} ({@code
 * CControl.load(layoutName)}). The slots share the properties file, their keys are prefixed with
 * {@code dock.slot.<name>.}.
 */
public final class DockLayoutStore {

    /** The name of the properties file inside the config directory. */
    public static final String FILE_NAME = "layout.properties";

    /**
     * The name of the slot applied at startup (Swing {@code DockingLayout.LAYOUT_NAMES[0]}: if
     * the user ever saved the {@code Default} arrangement, the UI starts with it).
     */
    public static final String DEFAULT_SLOT = "Default";

    private static final String KEY_PREFIX = "dock.";
    private static final String SLOT_PREFIX = "slot.";

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
     * Stores the open dockables per role, preserving any named layout slots already saved in the
     * file (read-modify-write — the Swing {@code CControl.writeXML} keeps all saved layouts, too).
     *
     * @param openDockables the ordered dockable ids per role
     * @throws IOException on I/O errors
     */
    public void save(Map<DockLocation, List<String>> openDockables) throws IOException {
        Properties properties = readProperties();
        for (DockLocation location : DockLocation.values()) {
            List<String> ids = openDockables.getOrDefault(location, List.of());
            properties.setProperty(KEY_PREFIX + location.name(), String.join(",", ids));
        }
        writeProperties(properties);
    }

    /**
     * Stores the given arrangement in the named layout slot, preserving the rest of the file
     * (Swing {@code SaveLayoutAction.actionPerformed}: {@code mainWindow.getDockControl()
     * .save(layoutName)}).
     *
     * @param name the slot name ({@code Default}, {@code Slot 1}, ...)
     * @param openDockables the ordered dockable ids per role
     * @throws IOException on I/O errors
     */
    public void saveSlot(String name, Map<DockLocation, List<String>> openDockables)
            throws IOException {
        Properties properties = readProperties();
        for (DockLocation location : DockLocation.values()) {
            List<String> ids = openDockables.getOrDefault(location, List.of());
            properties.setProperty(KEY_PREFIX + SLOT_PREFIX + name + "." + location.name(),
                String.join(",", ids));
        }
        writeProperties(properties);
    }

    /**
     * Loads the named layout slot, if the user ever saved one (Swing {@code LoadLayoutAction}
     * checks {@code CControl.layouts()} for the name before loading; the status line reports
     * "Layout &lt;name&gt; could not be found." otherwise).
     *
     * @param name the slot name
     * @return the ordered dockable ids per role, or empty if the slot was never saved
     * @throws IOException on I/O errors
     */
    public Optional<Map<DockLocation, List<String>>> loadSlot(String name) throws IOException {
        if (!Files.isRegularFile(file)) {
            return Optional.empty();
        }
        Properties properties = readProperties();
        // a slot is "defined" once its save wrote its keys (all three role keys are always written)
        if (properties.getProperty(KEY_PREFIX + SLOT_PREFIX + name + "."
            + DockLocation.LEFT.name()) == null) {
            return Optional.empty();
        }
        return Optional.of(parse(properties, KEY_PREFIX + SLOT_PREFIX + name + "."));
    }

    private Map<DockLocation, List<String>> parse(Properties properties, String keyPrefix) {
        EnumMap<DockLocation, List<String>> result = new EnumMap<>(DockLocation.class);
        for (DockLocation location : DockLocation.values()) {
            String value = properties.getProperty(keyPrefix + location.name(), "");
            List<String> ids = Arrays.stream(value.split(",")).map(String::trim)
                    .filter(s -> !s.isEmpty()).toList();
            result.put(location, ids);
        }
        return result;
    }

    private Properties readProperties() throws IOException {
        Properties properties = new Properties();
        if (Files.isRegularFile(file)) {
            try (var in = Files.newInputStream(file)) {
                properties.load(in);
            }
        }
        return properties;
    }

    private void writeProperties(Properties properties) throws IOException {
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
        try (var out = Files.newOutputStream(file)) {
            properties.store(out, "KeY JavaFX UI docking layout");
        }
    }

    /**
     * Loads the stored (last-state) layout.
     *
     * @return the ordered dockable ids per role; roles absent from the file (or missing file)
     *         yield empty lists
     * @throws IOException on I/O errors
     */
    public Map<DockLocation, List<String>> load() throws IOException {
        if (!Files.isRegularFile(file)) {
            EnumMap<DockLocation, List<String>> result = new EnumMap<>(DockLocation.class);
            for (DockLocation location : DockLocation.values()) {
                result.put(location, List.of());
            }
            return result;
        }
        return parse(readProperties(), KEY_PREFIX);
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
