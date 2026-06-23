/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.util.List;

import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ExceptionTools;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * When a {@code .key} file contains several independent syntax errors, all of them should be
 * reported (not just the first). A single error keeps the polished bail-path message (covered by
 * {@link KeYParserExceptionTest}); this test covers the multi-error path of
 * {@link ParsingFacade#parseFile}.
 *
 * @author Claude (improveErrorMessages)
 */
public class MultiSyntaxErrorTest {

    @Test
    public void reportsEveryIndependentSyntaxError() {
        // two function declarations each missing their terminating ';'
        String src = "\\functions {\n  int f\n  int g;\n  int h\n}\n\\problem { true }\n";
        var ex = assertThrows(RuntimeException.class,
            () -> ParsingFacade.parseFile(CharStreams.fromString(src)));

        List<PositionedString> msgs = ExceptionTools.getMessages(ex);
        assertTrue(msgs.size() >= 2,
            "both missing semicolons should be reported, but got: " + msgs);
        // Each error points at the insertion point of the missing ';' (the end of the declaration
        // on lines 2 and 4), not at the next, unexpected token (lines 3 and 5).
        var lines = msgs.stream().map(m -> m.getLocation().getPosition().line())
                .collect(java.util.stream.Collectors.toSet());
        assertTrue(lines.contains(2) && lines.contains(4),
            "errors should mark the missing ';' on lines 2 and 4, but got lines: " + lines);
    }

    @Test
    public void singleSyntaxErrorStaysAtOneMessage() {
        // regression guard: one error keeps the single-error (bail) path -> exactly one message
        String src = "\\problem {\n  (true & true\n}\n";
        var ex = assertThrows(RuntimeException.class,
            () -> ParsingFacade.parseFile(CharStreams.fromString(src)));
        List<PositionedString> msgs = ExceptionTools.getMessages(ex);
        assertEquals(1, msgs.size(), "a single error should produce a single message: " + msgs);
    }
}
