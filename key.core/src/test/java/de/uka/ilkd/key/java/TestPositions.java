package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import recoder.ProgramFactory;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.declaration.ParameterDeclaration;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class TestPositions {
    private static final ProgramFactory FACTORY = ProofJavaProgramFactory.getInstance();
    private static final Path TEST_FILE_PATH =
        Paths.get("src/test/resources/de/uka/ilkd/key/java/Positions.java");
    private static final Path EXPECTED_FILE_PATH =
        Paths.get("src/test/resources/de/uka/ilkd/key/java/Positions.txt");

    private static String formatPosition(SourceElement.Position p) {
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
                if (programElement instanceof ParameterDeclaration) {
                    int i = 0;
                }
                Assertions.assertEquals(expected, formatElement(programElement));
                i += 1;
            }
        }

        preorderTraverse(cu, new Consume());
    }
}
