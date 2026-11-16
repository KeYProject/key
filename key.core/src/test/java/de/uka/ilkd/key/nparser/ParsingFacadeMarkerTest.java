/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Tests for the marker-tolerant file parsing of {@link ParsingFacade} (§3 and §7.2 of the
 * headless interface spec): the status marker is a line comment, so the lexer hides it and the
 * token positions still refer to the original file.
 */
class ParsingFacadeMarkerTest {

    private static final String BODY = "\\problem { true }\n";

    private static Path writeTempFile(String content) throws IOException {
        Path file = Files.createTempFile("parsingFacadeMarker", ".key");
        Files.writeString(file, content);
        return file;
    }

    @Test
    void closedMarkerCommentIsIgnored() throws IOException {
        Path plain = writeTempFile(BODY);
        Path marked = writeTempFile("// KEY_PROOF_STATUS closed 0\n" + BODY);

        KeyAst.File plainAst = ParsingFacade.parseFile(plain);
        KeyAst.File markedAst = ParsingFacade.parseFile(marked);

        var plainCtx = ParsingFacade.getParseRuleContext(plainAst);
        var markedCtx = ParsingFacade.getParseRuleContext(markedAst);
        assertEquals(plainCtx.getText(), markedCtx.getText(),
            "the marker comment must not be visible to the parser");
        // positions refer to the original file: \problem starts on line 2 of the marked file
        assertEquals(1, plainCtx.problem().getStart().getLine());
        assertEquals(2, markedCtx.problem().getStart().getLine());
    }

    @Test
    void openMarkerCommentIsIgnored() throws IOException {
        Path plain = writeTempFile(BODY);
        Path marked = writeTempFile("// KEY_PROOF_STATUS open 3\n" + BODY);

        var plainCtx = ParsingFacade.getParseRuleContext(ParsingFacade.parseFile(plain));
        var markedCtx = ParsingFacade.getParseRuleContext(ParsingFacade.parseFile(marked));

        assertEquals(plainCtx.getText(), markedCtx.getText());
        assertEquals(2, markedCtx.problem().getStart().getLine());
    }

    @Test
    void markerCommentWithCrlfIsIgnored() throws IOException {
        Path plain = writeTempFile(BODY);
        Path marked = writeTempFile("// KEY_PROOF_STATUS closed 0\r\n" + BODY);

        var plainCtx = ParsingFacade.getParseRuleContext(ParsingFacade.parseFile(plain));
        var markedCtx = ParsingFacade.getParseRuleContext(ParsingFacade.parseFile(marked));

        assertEquals(plainCtx.getText(), markedCtx.getText());
    }

    @Test
    void fileStartingWithProfileIsUnaffected() throws IOException {
        String content = "\\profile \"Java Profile\";\n\n\\problem { true }\n";
        Path file = writeTempFile(content);

        var ctx = ParsingFacade.getParseRuleContext(ParsingFacade.parseFile(file));

        assertNotNull(ctx.profile());
        assertEquals(1, ctx.profile().getStart().getLine());
        assertNotNull(ctx.problem());
        assertEquals(3, ctx.problem().getStart().getLine());
    }
}
