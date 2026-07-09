/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.IOException;
import java.io.StringWriter;

import de.uka.ilkd.key.settings.StrategyPresetsSettings.StrategyPreset;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link StrategyPresetsSettings}: the in-memory bookkeeping (add / overwrite / stash /
 * rename / remove) and the {@link Configuration} persistence round-trip.
 */
class StrategyPresetsSettingsTest {

    private static StrategyProperties props(String splitting, String loop) {
        StrategyProperties p = new StrategyProperties();
        p.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, splitting);
        p.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loop);
        return p;
    }

    @Test
    void saveKeepsInsertionOrderAndOverwritesByName() {
        StrategyPresetsSettings s = new StrategyPresetsSettings();
        s.saveOrUpdate(new StrategyPreset("arith", 4000,
            props(StrategyProperties.SPLITTING_OFF, StrategyProperties.LOOP_NONE)));
        s.saveOrUpdate(new StrategyPreset("loops", 8000,
            props(StrategyProperties.SPLITTING_NORMAL, StrategyProperties.LOOP_INVARIANT)));

        assertEquals(2, s.getPresets().size());
        assertEquals("arith", s.getPresets().get(0).name());
        assertEquals("loops", s.getPresets().get(1).name());

        // overwriting an existing name keeps its position but replaces the payload
        s.saveOrUpdate(new StrategyPreset("arith", 1234,
            props(StrategyProperties.SPLITTING_DELAYED, StrategyProperties.LOOP_EXPAND)));
        assertEquals(2, s.getPresets().size());
        assertEquals("arith", s.getPresets().get(0).name());
        assertEquals(1234, s.getPreset("arith").orElseThrow().maxSteps());
    }

    @Test
    void stashUsesReservedSingleSlot() {
        StrategyPresetsSettings s = new StrategyPresetsSettings();
        s.stash(5000, props(StrategyProperties.SPLITTING_OFF, StrategyProperties.LOOP_NONE));
        s.stash(6000, props(StrategyProperties.SPLITTING_NORMAL, StrategyProperties.LOOP_EXPAND));

        assertEquals(1, s.getPresets().size(), "stashing twice must not create a second slot");
        StrategyPreset stash = s.getPreset(StrategyPresetsSettings.STASH_NAME).orElseThrow();
        assertEquals(6000, stash.maxSteps());
        assertEquals(StrategyProperties.SPLITTING_NORMAL,
            stash.properties().getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY));
    }

    @Test
    void renameRejectsCollisionAndUpdatesOtherwise() {
        StrategyPresetsSettings s = new StrategyPresetsSettings();
        s.saveOrUpdate(new StrategyPreset("a", 1, props(StrategyProperties.SPLITTING_OFF,
            StrategyProperties.LOOP_NONE)));
        s.saveOrUpdate(new StrategyPreset("b", 2, props(StrategyProperties.SPLITTING_OFF,
            StrategyProperties.LOOP_NONE)));

        assertFalse(s.rename("a", "b"), "must not rename onto an existing name");
        assertTrue(s.contains("a"));

        assertTrue(s.rename("a", "c"));
        assertFalse(s.contains("a"));
        assertTrue(s.contains("c"));
        assertEquals(1, s.getPreset("c").orElseThrow().maxSteps());
    }

    @Test
    void removeDropsPreset() {
        StrategyPresetsSettings s = new StrategyPresetsSettings();
        s.saveOrUpdate(new StrategyPreset("a", 1, props(StrategyProperties.SPLITTING_OFF,
            StrategyProperties.LOOP_NONE)));
        assertTrue(s.remove("a"));
        assertFalse(s.remove("a"));
        assertTrue(s.getPresets().isEmpty());
    }

    @Test
    void configurationRoundTripPreservesEverything() throws IOException {
        StrategyPresetsSettings original = new StrategyPresetsSettings();
        original.saveOrUpdate(new StrategyPreset("arith", 4000,
            props(StrategyProperties.SPLITTING_OFF, StrategyProperties.LOOP_NONE)));
        original.saveOrUpdate(new StrategyPreset("loops", 8000,
            props(StrategyProperties.SPLITTING_NORMAL, StrategyProperties.LOOP_INVARIANT)));
        original.stash(5000, props(StrategyProperties.SPLITTING_DELAYED,
            StrategyProperties.LOOP_EXPAND));

        // write -> serialize to text -> reparse -> read (mirrors the actual settings file path)
        Configuration written = new Configuration();
        original.writeSettings(written);
        StringWriter out = new StringWriter();
        written.save(out, "");
        Configuration reparsed = Configuration.load(CharStreams.fromString(out.toString()));

        StrategyPresetsSettings restored = new StrategyPresetsSettings();
        restored.readSettings(reparsed);

        assertEquals(3, restored.getPresets().size());
        assertEquals("arith", restored.getPresets().get(0).name());
        assertEquals("loops", restored.getPresets().get(1).name());
        assertEquals(StrategyPresetsSettings.STASH_NAME, restored.getPresets().get(2).name());

        StrategyPreset arith = restored.getPreset("arith").orElseThrow();
        assertEquals(4000, arith.maxSteps());
        assertEquals(StrategyProperties.SPLITTING_OFF,
            arith.properties().getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY));
        assertEquals(StrategyProperties.LOOP_NONE,
            arith.properties().getProperty(StrategyProperties.LOOP_OPTIONS_KEY));

        StrategyPreset loops = restored.getPreset("loops").orElseThrow();
        assertEquals(8000, loops.maxSteps());
        assertEquals(StrategyProperties.LOOP_INVARIANT,
            loops.properties().getProperty(StrategyProperties.LOOP_OPTIONS_KEY));
    }

    @Test
    void readingEmptyConfigurationYieldsNoPresets() {
        StrategyPresetsSettings s = new StrategyPresetsSettings();
        s.readSettings(new Configuration());
        assertTrue(s.getPresets().isEmpty());
    }
}
