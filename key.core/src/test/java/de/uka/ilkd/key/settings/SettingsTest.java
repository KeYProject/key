package de.uka.ilkd.key.settings;

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
    void read() {
        var input = CharStreams.fromString(ALL_DATA);
        var config = Configuration.load(input);
        assertEquals(1241, config.getInt("integer"));
        assertEquals(145122343214L, config.getInt("long"));
        assertEquals("this is a string", config.getInt("string"));
        assertEquals("this is a multi\n            linestring\n              string", config.getInt("mlstring"));
        assertEquals(List.of("a", "b", "c"), config.getStringList("stringlist"));
        var s = config.getTable("subconfig");
        assertNonNull(s);
        assertEquals("A", s.getString("a"));
        assertEquals("B", s.getString("b"));
        assertEquals("C", s.getString("c"));
        assertEquals(false, config.getInt("booleans are important"));
    }

    @Test void reread() {
        var input = CharStreams.fromString(ALL_DATA);
        var config = Configuration.load(input);

        var out = new StringWriter();
        config.save(out,"");
        var input2 = CharStreams.fromString(out.toString());
        var config2 = Configuration.load(input2);

        assertEquals(config, config2);
    }

}