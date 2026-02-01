/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.IOException;
import java.io.StringWriter;
import java.util.List;

import de.uka.ilkd.key.nparser.ParsingFacade;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
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


    @Test
    void proofSettings() {
        var ssettings =
            """
                    {
                        "Strategy" : {
                            "ActiveStrategy" : "JavaCardDLStrategy",
                            "MaximumNumberOfAutomaticApplications" : 10000,
                            "Timeout" : -1,
                            "options" : {
                                "AUTO_INDUCTION_OPTIONS_KEY" : "AUTO_INDUCTION_OFF",
                                "BLOCK_OPTIONS_KEY" : "BLOCK_CONTRACT_INTERNAL",
                                "CLASS_AXIOM_OPTIONS_KEY" : "CLASS_AXIOM_FREE",
                                "DEP_OPTIONS_KEY" : "DEP_ON",
                                "INF_FLOW_CHECK_PROPERTY" : "INF_FLOW_CHECK_FALSE",
                                "LOOP_OPTIONS_KEY" : "LOOP_SCOPE_INV_TACLET",
                                "METHOD_OPTIONS_KEY" : "METHOD_CONTRACT",
                                "MPS_OPTIONS_KEY" : "MPS_MERGE",
                                "NON_LIN_ARITH_OPTIONS_KEY" : "NON_LIN_ARITH_DEF_OPS",
                                "OSS_OPTIONS_KEY" : "OSS_ON",
                                "QUANTIFIERS_OPTIONS_KEY" : "QUANTIFIERS_NON_SPLITTING_WITH_PROGS",
                                "QUERYAXIOM_OPTIONS_KEY" : "QUERYAXIOM_ON",
                                "QUERY_NEW_OPTIONS_KEY" : "QUERY_OFF",
                                "SPLITTING_OPTIONS_KEY" : "SPLITTING_DELAYED",
                                "STOPMODE_OPTIONS_KEY" : "STOPMODE_DEFAULT",
                                "SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY" : "SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER",
                                "SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY" : "SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF",
                                "USER_TACLETS_OPTIONS_KEY1" : "USER_TACLETS_OFF",
                                "USER_TACLETS_OPTIONS_KEY2" : "USER_TACLETS_OFF",
                                "USER_TACLETS_OPTIONS_KEY3" : "USER_TACLETS_OFF",
                                "VBT_PHASE" : "VBT_SYM_EX"
                             }
                         }
                     }""";


        var stratSettings = new StrategySettings();
        var config = ParsingFacade.readConfigurationFile(CharStreams.fromString(ssettings));
        stratSettings.readSettings(config);
        var actual = stratSettings.writeSettingsToString();
        assertThat(actual).isEqualToIgnoringWhitespace(ssettings);
    }

}
