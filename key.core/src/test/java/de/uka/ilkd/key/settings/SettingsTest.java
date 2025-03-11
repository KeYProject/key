/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.IOException;
import java.io.StringWriter;
import java.util.List;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class SettingsTest {
    enum ABC {
        A, B, C;
    }

    static final String ALL_DATA = """
            {
                integer : 1241,
                long     : 145122343214L,
                string   : "this is a string",
                mlstring : "this is a multi
                    linestring
                    string",
                stringlist : ["a", "b", "c"],
                subconfig  : {
                    a : "A",
                    b : "B",
                    c : "C",
                },
                "booleans are important": true,
                "booleans are important": false,
            }
            """;

    @Test
    void read() throws IOException {
        var input = CharStreams.fromString(ALL_DATA);
        var config = Configuration.load(input);
        assertEquals(1241, config.getInt("integer"));
        assertEquals(145122343214L, config.getLong("long"));
        assertEquals("this is a string", config.getString("string"));
        assertEquals("this is a multi\n        linestring\n        string",
            config.getString("mlstring"));
        assertEquals(List.of("a", "b", "c"), config.getStringList("stringlist"));
        var s = config.getTable("subconfig");
        assertNotNull(s);
        assertEquals("A", s.getString("a"));
        assertEquals("B", s.getString("b"));
        assertEquals("C", s.getString("c"));

        assertEquals(ABC.A, s.getEnum("a", ABC.C));
        assertEquals(ABC.B, s.getEnum("b", ABC.A));
        assertEquals(ABC.C, s.getEnum("c", ABC.B));

        assertFalse(config.getBool("booleans are important"));
    }

    @Test
    void reread() throws IOException {
        var input = CharStreams.fromString(ALL_DATA);
        var config = Configuration.load(input);

        var out = new StringWriter();
        config.save(out, "");
        var input2 = CharStreams.fromString(out.toString());
        var config2 = Configuration.load(input2);

        assertEquals(config, config2);
    }

}
