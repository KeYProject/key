/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The {@code --json} CLI output is the OpenAI tool format extended with the KeY-side category and
 * background metadata.
 */
class CliMetadataTest {

    @Test
    void jsonCliOutputCarriesCategoryAndBackground() {
        var json = KeYAgentTools.cliDocumentation(true);
        assertTrue(json.contains("\"category\": \"Shell\""), json);
        assertTrue(json.contains("\"backgroundable\": true"), json);
        // the plain OpenAI keys are still present
        assertTrue(json.contains("\"parameters\""), json);
    }
}
