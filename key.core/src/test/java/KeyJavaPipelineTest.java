/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.transformations.KeYJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.proof.init.JavaProfile;

import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.DefaultPrettyPrinterVisitor;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.google.common.truth.Truth;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
class KeyJavaPipelineTest {
    public KeYJavaPipeline createPipelineTest(Path testFolder) throws IOException {
        Services services = new Services(JavaProfile.getDefaultProfile());
        var js = services.activateJava(null, Collections.singleton(testFolder));

        var inputFolder = testFolder.resolve("input");
        final var jp = js.getProgramFactory().createJavaParser();
        var files = Files.list(inputFolder);
        var cu = new ArrayList<CompilationUnit>();
        files.forEach(it -> {
            try {
                ParseResult<CompilationUnit> r = jp.parse(it);
                if (!r.isSuccessful()) {
                    for (Problem problem : r.getProblems()) {
                        System.err.println(problem);
                    }
                    throw new IllegalStateException();
                }
                var c = r.getResult().get();
                cu.add(c);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });
        var tservices =
            new TransformationPipelineServices(services.getJavaService().getProgramFactory(),
                new TransformationPipelineServices.TransformerCache(cu));
        var kjp = KeYJavaPipeline.createDefault(tservices);
        var kjp2 = new KeYJavaPipeline(tservices);
        var cnt = 0;
        for (JavaTransformer step : kjp.getSteps()) {
            kjp2.add(step);
            final var file = testFolder.resolve("actual").resolve(
                String.format("%02d_%s", ++cnt, step.getClass().getSimpleName()));
            kjp2.add(new DebugOutputTransformer(file, tservices));
        }
        return kjp2;
    }

    @TestFactory
    Stream<DynamicTest> simple() throws IOException {
        return generatePipelineTests(Paths.get("pipelineTests/simple").toAbsolutePath());
    }

    private Stream<DynamicTest> generatePipelineTests(Path testFolder) throws IOException {
        var pt = createPipelineTest(testFolder);
        pt.apply();
        var expected = testFolder.resolve("expected");
        var actual = testFolder.resolve("actual");

        return Files.walk(expected)
                .filter(Files::isRegularFile)
                .map(it -> DynamicTest.dynamicTest(it.toString(),
                    () -> checkEqualFile(it, expected, actual)));
    }

    private void checkEqualFile(Path expectedFile, Path expectedFolder, Path actualFolder)
            throws IOException {
        var actualFile = actualFolder.resolve(expectedFolder.relativize(expectedFile));
        if (!Files.exists(actualFile)) {
            Assertions.fail("Actual file " + actualFile + " does not exists.");
        }
        var expected = Files.readString(expectedFile);
        var actual = Files.readString(actualFile);

        Truth.assertThat(actual).isEqualTo(expected);
    }

    private static class DebugOutputTransformer extends JavaTransformer {
        final Path outputFolder;
        final Set<Path> alreadyWritten = new HashSet<>();
        private static final Logger LOGGER = LoggerFactory.getLogger(DebugOutputTransformer.class);
        private final Printer myPrinter = new DefaultPrettyPrinter(
            MyPrintVisitor::new,
            new DefaultPrinterConfiguration());


        public DebugOutputTransformer(Path s, TransformationPipelineServices services) {
            super(services);
            outputFolder = s;
        }

        @Override
        public void apply(TypeDeclaration<?> td) {
            try {
                Files.createDirectories(outputFolder);
            } catch (IOException e) {
                e.printStackTrace();
            }
            for (CompilationUnit unit : services.getCache().getUnits()) {
                var name = unit.getPrimaryTypeName().get();
                var file = outputFolder.resolve(name + ".java");
                if (!alreadyWritten.contains(file)) {
                    alreadyWritten.add(file);
                    try {
                        unit.printer(myPrinter);
                        Files.writeString(file, unit.toString());
                    } catch (IOException e) {
                        LOGGER.error(e.getMessage(), e);
                    }
                }
            }
        }
    }

    private static class MyPrintVisitor extends DefaultPrettyPrinterVisitor {
        public MyPrintVisitor(PrinterConfiguration configuration) {
            super(configuration);
        }
    }
}
