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

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Persists the docking layout (which dockables are open in which {@link DockLocation role}) in a
 * plain {@link Properties} file inside the KeY configuration directory.
 * <p>
 * Counter-part of the Docking Frames {@code layout.xml} persistence of the Swing module
 * {@code key.ui}; the file format is deliberately simple and self-contained. The actual
 * sequence of "which dockable belongs to which role" is the persisted content; the divider
 * positions of the main-area SplitPane are persisted as well (reviewer request: the separator
 * position is restored accurately), floating windows are not persisted (yet).
 * <p>
 * Beyond the plain (last-state) layout the store keeps <em>named layout slots</em> — the counter
 * part of the Swing {@code DockingLayout} arrangements {@code Default}/{@code Slot 1}/{@code
 * Slot 2}, which the user fills via {@code View > Layout > Save ...} (Swing {@code
 * SaveLayoutAction}: {@code CControl.save(layoutName)}) and recalls via {@code Load ...} ({@code
 * CControl.load(layoutName)}). The slots share the properties file, their keys are prefixed with
 * {@code dock.slot.<name>.}.
 */
public final class DockLayoutStore {

    private static final Logger LOGGER = LoggerFactory.getLogger(DockLayoutStore.class);

    /** The factory default west divider position of the main-area SplitPane. */
    public static final double DEFAULT_WEST_DIVIDER = 0.18;

    /** The factory default east divider position of the main-area SplitPane. */
    public static final double DEFAULT_EAST_DIVIDER = 0.86;

    private static final String MAIN_SPLIT_WEST_KEY = "main.split.westDivider";
    private static final String MAIN_SPLIT_EAST_KEY = "main.split.eastDivider";

    /**
     * The name of the properties file inside the config directory.
     */
    public static final String FILE_NAME = "layout.properties";

    /**
     * The layout format version, persisted next to the roles. Bumped when the set of dockable
     * roles changes incompatibly (MP10 removed the left/right dockables): files written by an
     * older version are discarded so stale persisted layouts fall back to the factory default
     * instead of half-restoring references to dockables that no longer exist.
     */
    private static final int LAYOUT_VERSION = 2;
    private static final String VERSION_KEY = "dock.version";

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
        properties.setProperty(VERSION_KEY, String.valueOf(LAYOUT_VERSION));
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
        properties.setProperty(VERSION_KEY, String.valueOf(LAYOUT_VERSION));
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
        if (!isVersionCompatible(properties)) {
            return Optional.empty();
        }
        // a slot is "defined" once its save wrote its keys (all three role keys are always written)
        if (properties.getProperty(KEY_PREFIX + SLOT_PREFIX + name + "."
            + DockLocation.LEFT.name()) == null) {
            return Optional.empty();
        }
        return Optional.of(parse(properties, KEY_PREFIX + SLOT_PREFIX + name + "."));
    }

    /**
     * Stores the divider positions of the main-area SplitPane (reviewer request: the separator
     * position is stored to restore the layout accurately — Swing persisted the full
     * {@code CControl} layout XML including the splitter positions). The keys share the layout
     * properties file; missing entries fall back to the factory default positions.
     *
     * @param west the west divider position (the fraction of the main area left of the west
     *        divider)
     * @param east the east divider position (the fraction of the main area left of the east
     *        divider)
     * @throws IOException on I/O errors
     */
    public void saveMainSplitDividers(double west, double east) throws IOException {
        Properties properties = readProperties();
        properties.setProperty(MAIN_SPLIT_WEST_KEY, Double.toString(west));
        properties.setProperty(MAIN_SPLIT_EAST_KEY, Double.toString(east));
        writeProperties(properties);
    }

    /**
     * Loads the divider positions of the main-area SplitPane, falling back to the factory
     * defaults (west {@code 0.18}, east {@code 0.86}) when the entries are missing or
     * malformed.
     *
     * @return the west and east divider positions in the range {@code [0, 1]}
     */
    public double[] loadMainSplitDividers() {
        Properties properties = new Properties();
        try {
            if (Files.isRegularFile(file)) {
                try (var in = Files.newInputStream(file)) {
                    properties.load(in);
                }
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to read the main split divider positions", e);
            return new double[] { DEFAULT_WEST_DIVIDER, DEFAULT_EAST_DIVIDER };
        }
        try {
            double west = Double.parseDouble(properties.getProperty(MAIN_SPLIT_WEST_KEY,
                Double.toString(DEFAULT_WEST_DIVIDER)));
            double east = Double.parseDouble(properties.getProperty(MAIN_SPLIT_EAST_KEY,
                Double.toString(DEFAULT_EAST_DIVIDER)));
            west = Math.max(0.0, Math.min(1.0, west));
            east = Math.max(0.0, Math.min(1.0, east));
            if (east < west) {
                return new double[] { DEFAULT_WEST_DIVIDER, DEFAULT_EAST_DIVIDER };
            }
            return new double[] { west, east };
        } catch (NumberFormatException e) {
            return new double[] { DEFAULT_WEST_DIVIDER, DEFAULT_EAST_DIVIDER };
        }
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
        Properties properties = readProperties();
        if (!isVersionCompatible(properties)) {
            // stale layout written before the MP10 dockable-role change: discard it so the
            // workspace falls back to the factory default layout
            clear();
            EnumMap<DockLocation, List<String>> result = new EnumMap<>(DockLocation.class);
            for (DockLocation location : DockLocation.values()) {
                result.put(location, List.of());
            }
            return result;
        }
        return parse(properties, KEY_PREFIX);
    }

    /**
     * @param properties the persisted properties
     * @return whether the file carries the current layout version (files without the version key
     *         are pre-MP10 and stale)
     */
    private boolean isVersionCompatible(Properties properties) {
        try {
            return Integer.parseInt(properties.getProperty(VERSION_KEY, "-1")) == LAYOUT_VERSION;
        } catch (NumberFormatException e) {
            return false;
        }
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
