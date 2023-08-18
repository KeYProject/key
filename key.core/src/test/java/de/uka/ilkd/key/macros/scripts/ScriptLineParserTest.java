/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;

import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (7/25/21)
 */
public class ScriptLineParserTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ScriptLineParserTest.class);

    @Test
    public void test() throws Exception {
        String arg = "macro key1=value1 key2=\"value two\" defval3 \"long defvalue\"; "
            + "command ; \n\n" + "# some comment\n"
            + "multiline #comment internal\n command \n with=\"line breaks in \n values\"; \n"
            + "select formula=\"a;b\"; \n" + "hyphened-command;\n";

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(arg), null);
        ScriptLineParser.ParsedCommand command;
        while ((command = mlp.parseCommand()) != null) {
            LOGGER.info(String.valueOf(command.args));
        }
    }
}
