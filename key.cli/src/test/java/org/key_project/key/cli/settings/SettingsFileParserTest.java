/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.settings;

import java.util.Map;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

/**
 * Tests for {@link SettingsFileParser}: parsing of the §5.2 settings JSON into a
 * {@code category -> "category:value"} map and rejection of unknown keys or undocumented values
 * with the exact violating line.
 */
class SettingsFileParserTest {

    private final SettingsFileParser parser = new SettingsFileParser();

    @Test
    void fullSettingsExampleParsesEveryKey() {
        String json = """
                {
                  "intRules": "intRules:javaSemantics",
                  "integerSimplificationRules": "integerSimplificationRules:full",
                  "javaLoopTreatment": "javaLoopTreatment:efficient",
                  "assertions": "assertions:safe",
                  "runtimeExceptions": "runtimeExceptions:ban",
                  "bigint": "bigint:on",
                  "programRules": "programRules:Java",
                  "methodExpansion": "methodExpansion:modularOnly",
                  "Strings": "Strings:on",
                  "sequences": "sequences:on",
                  "reach": "reach:on",
                  "permissions": "permissions:off"
                }
                """;

        Map<String, String> settings = parser.parse(json);

        assertThat(settings).hasSize(12);
        assertThat(settings).containsEntry("intRules", "intRules:javaSemantics");
        assertThat(settings).containsEntry("integerSimplificationRules",
            "integerSimplificationRules:full");
        assertThat(settings).containsEntry("javaLoopTreatment", "javaLoopTreatment:efficient");
        assertThat(settings).containsEntry("assertions", "assertions:safe");
        assertThat(settings).containsEntry("runtimeExceptions", "runtimeExceptions:ban");
        assertThat(settings).containsEntry("bigint", "bigint:on");
        assertThat(settings).containsEntry("programRules", "programRules:Java");
        assertThat(settings).containsEntry("methodExpansion", "methodExpansion:modularOnly");
        assertThat(settings).containsEntry("Strings", "Strings:on");
        assertThat(settings).containsEntry("sequences", "sequences:on");
        assertThat(settings).containsEntry("reach", "reach:on");
        assertThat(settings).containsEntry("permissions", "permissions:off");
    }

    @Test
    void intRulesCheckedIsAccepted() {
        Map<String, String> settings = parser.parse("{\"intRules\": \"intRules:checked\"}");
        assertThat(settings).containsEntry("intRules", "intRules:checked");
    }

    @Test
    void intRulesUncheckedIsAccepted() {
        Map<String, String> settings = parser.parse("{\"intRules\": \"intRules:unchecked\"}");
        assertThat(settings).containsEntry("intRules", "intRules:unchecked");
    }

    @Test
    void unknownKeyCarriesTheOffendingLine() {
        String json = """
                {
                  "intRules": "intRules:javaSemantics",
                  "unsupportedKey": "x"
                }
                """;

        assertThatThrownBy(() -> parser.parse(json))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("unsupportedKey")
                .hasMessageContaining("not understood");
    }

    @Test
    void typoValueCarriesTheOffendingLine() {
        String json = """
                {
                  "intRules": "intRules:javaSemantic"
                }
                """;

        assertThatThrownBy(() -> parser.parse(json))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("intRules:javaSemantic")
                .hasMessageContaining("not understood");
    }

    @Test
    void eachDocumentedValueOfEveryKeyIsAccepted() {
        String json = """
                {
                  "intRules": "intRules:arithmeticSemanticsIgnoringOF",
                  "integerSimplificationRules": "integerSimplificationRules:standard",
                  "javaLoopTreatment": "-javaLoopTreatment",
                  "assertions": "assertions:off",
                  "runtimeExceptions": "runtimeExceptions:allow",
                  "bigint": "bigint:off",
                  "programRules": "programRules:JavaCard",
                  "methodExpansion": "methodExpansion:full",
                  "Strings": "Strings:off",
                  "sequences": "sequences:off",
                  "reach": "reach:off",
                  "permissions": "permissions:on"
                }
                """;

        assertThat(parser.parse(json)).hasSize(12);
    }

    @Test
    void emptyObjectParsesToNoSettings() {
        assertThat(parser.parse("{}")).isEmpty();
    }
}
