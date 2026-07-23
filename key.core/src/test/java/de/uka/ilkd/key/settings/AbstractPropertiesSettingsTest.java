/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Regression tests for {@link AbstractPropertiesSettings} numeric properties: a stored value may
 * deserialize as {@link Integer} or {@link Long} depending on its magnitude and the settings
 * format,
 * and reading it back must not depend on which boxed type it happens to be (it used to crash KeY on
 * startup with a {@code ClassCastException}).
 */
public class AbstractPropertiesSettingsTest {

    private static final class TestSettings extends AbstractPropertiesSettings {
        final PropertyEntry<Integer> intProp;

        TestSettings() {
            super("TestCat");
            intProp = createIntegerProperty("myInt", 7);
        }
    }

    @Test
    public void readsIntegerPropertyStoredAsInteger() {
        Configuration cfg = new Configuration();
        cfg.getOrCreateSection("TestCat").set("myInt", 42); // stored as Integer
        TestSettings settings = new TestSettings();
        settings.readSettings(cfg);
        assertEquals(42, settings.intProp.get());
    }

    @Test
    public void readsIntegerPropertyStoredAsLong() {
        Configuration cfg = new Configuration();
        cfg.getOrCreateSection("TestCat").set("myInt", Long.valueOf(42)); // stored as Long
        TestSettings settings = new TestSettings();
        settings.readSettings(cfg);
        assertEquals(42, settings.intProp.get());
    }
}
