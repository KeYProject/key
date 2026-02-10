/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.nparser.ParsingFacade;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * @author Alexander Weigl
 * @version 1 (7/25/21)
 */
public class ProofScriptParserTest {
    @Test
    public void test() throws Exception {
        String arg = """
                macro key1=value1 key2="value two" defval3 "long defvalue"; command ;\s

                # some comment
                multiline #comment internal
                 command\s
                 with="line breaks in\s
                 values";\s
                select formula="a;b";\s
                hyphenedCommand;
                """;

        var script = ParsingFacade.parseScript(arg);
        var ast = script.asAst();
        for (var scriptCommandAst : ast) {
            System.out.println(scriptCommandAst);
        }
    }

    @Test
    void higherOrder() {
        String arg = """
                cmd key1: { cmd1; }\s
                    key2: { cmd2; };\s
                cmd { cmd; } { cmd; };
                cmd { cmd; } { cmd; };
                """;

        var script = ParsingFacade.parseScript(arg);
        var ast = script.asAst();
        for (var scriptCommandAst : ast) {
            System.out.println(scriptCommandAst);
        }

        assertThat(ast).hasSize(3);

        var cmd1 = ast.get(0);
        var cmd2 = ast.get(1);
        var cmd3 = ast.get(2);

        assertThat(cmd1.commandName()).isEqualTo("cmd");
        assertThat(cmd1.namedArgs()).containsKey("key1");
        assertThat(cmd1.namedArgs()).containsKey("key2");

        assertThat(cmd2.positionalArgs()).hasSize(2);
        assertThat(cmd3.positionalArgs()).hasSize(2);
    }
}
