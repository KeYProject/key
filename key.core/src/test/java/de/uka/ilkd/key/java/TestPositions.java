/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import recoder.ProgramFactory;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;

/**
 * This class checks the position information returned by the proof java parser
 * {@link de.uka.ilkd.key.parser.proofjava.ProofJavaParser}.
 * The path to the test file and the oracle .txt file can be found below.
 */
public class TestPositions {
    private static final ProgramFactory FACTORY = ProofJavaProgramFactory.getInstance();

    /** Test file, does not contain sensible java, only parseable */
    private static final Path TEST_FILE_PATH =
        Paths.get("src/test/resources/de/uka/ilkd/key/java/Positions.java");
    /**
     * Oracle file, regenerate by uncommenting the call to {@link #generate(ProgramElement)} below.
     */
    private static final Path EXPECTED_FILE_PATH =
        Paths.get("src/test/resources/de/uka/ilkd/key/java/Positions.txt");

    private static String formatPosition(SourceElement.Position p) {
        // Do not rely on SourceElement.Position.toString, might change
        if (p != SourceElement.Position.UNDEFINED) {
            return new StringBuilder()
                    .append(p.getLine()).append('/').append(p.getColumn())
                    .toString();
        } else {
            return "??/??";
        }
    }

    private static void preorderTraverse(ProgramElement element,
            Consumer<ProgramElement> consumer) {
        consumer.accept(element);
        if (!(element instanceof NonTerminalProgramElement)) {
            return;
        }
        var e = ((NonTerminalProgramElement) element);
        var n = e.getChildCount();
        for (int i = 0; i < n; ++i) {
            preorderTraverse(e.getChildAt(i), consumer);
        }
    }

    private static String formatElement(ProgramElement e) {
        return e.getClass().getName() + "," + formatPosition(e.getStartPosition()) + ","
            + formatPosition(e.getEndPosition());
    }

    @SuppressWarnings("unused")
    private static void generate(ProgramElement element) {
        preorderTraverse(element, e -> System.out.println(formatElement(e)));
    }

    @Test
    public void testPositionsFile() {
        var cu = Assertions.assertDoesNotThrow(() -> {
            try (var reader = Files.newBufferedReader(TEST_FILE_PATH)) {
                return FACTORY.parseCompilationUnit(reader);
            }
        }, "Parse test file");

        // Uncomment this to print a new oracle to the console
        // generate(cu);

        var expectedValues = Assertions.assertDoesNotThrow(() -> {
            try (var reader = Files.newBufferedReader(EXPECTED_FILE_PATH)) {
                return reader.lines()
                        .filter(l -> !l.isEmpty())
                        .map(String::trim)
                        .collect(Collectors.toList());
            }
        }, "Read expected file");

        class Consume implements Consumer<ProgramElement> {
            int i = 0;

            @Override
            public void accept(ProgramElement programElement) {
                Assertions.assertTrue(i < expectedValues.size(),
                    "Didn't expect that many program elements");
                var expected = expectedValues.get(i);
                Assertions.assertEquals(expected, formatElement(programElement));
                i += 1;
            }
        }

        var consumer = new Consume();
        preorderTraverse(cu, consumer);
        Assertions.assertEquals(expectedValues.size(), consumer.i,
            "Expected more program elements");
    }
}
