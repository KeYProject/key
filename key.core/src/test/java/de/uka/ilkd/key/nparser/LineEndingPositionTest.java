/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Guards that the source position reported for an error inside a Java modality block does not
 * depend
 * on the file's line-ending style: a Windows (CRLF) file must yield the same line/column as the
 * equivalent Unix (LF) file. {@code ExpressionBuilder} maps the block-relative error position back
 * into the {@code .key} file by counting {@code '\n'}; a stray {@code '\r'} always sits immediately
 * before its {@code '\n'} and so must not shift the result. {@code CharStreams.fromPath} does not
 * normalise line endings, so this exercises the real CRLF code path.
 *
 * @author Claude (improveErrorMessages)
 */
public class LineEndingPositionTest {

    // A Java block with an unresolved type 'Foobar' on the SECOND line of the block, i.e. line 3 of
    // the .key file, at column 8 (seven leading spaces). The error must map to exactly that spot
    // regardless of whether the file uses LF or CRLF.
    private static final String LF =
        "\\problem {\n   \\<{ int i;\n       Foobar x; }\\> true\n}\n";

    private static Position errorPosition(String content) throws Exception {
        Path f = Files.createTempFile("lineEnding", ".key");
        Files.writeString(f, content);
        try {
            KeYEnvironment.load(f);
            fail("expected the Java block to fail loading: " + content);
            throw new IllegalStateException("unreachable");
        } catch (Throwable t) {
            Location loc = ExceptionTools.getLocation(t);
            assertNotNull(loc, "a location is expected for: " + content);
            return loc.getPosition();
        } finally {
            Files.deleteIfExists(f);
        }
    }

    @Test
    public void javaBlockErrorPositionIsLineEndingAgnostic() throws Exception {
        Position lf = errorPosition(LF);
        Position crlf = errorPosition(LF.replace("\n", "\r\n"));

        // Sanity: the LF case points at 'Foobar' (file line 3, column 8).
        assertEquals(3, lf.line(), "LF: should point at the Java block line holding 'Foobar'");
        assertEquals(8, lf.column(), "LF: should point at the 'Foobar' identifier");

        // The CRLF file must report the very same position.
        assertEquals(lf.line(), crlf.line(), "line must not depend on CR/LF");
        assertEquals(lf.column(), crlf.column(), "column must not depend on CR/LF");
    }
}
