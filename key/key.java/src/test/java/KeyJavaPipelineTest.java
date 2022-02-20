import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.DefaultPrettyPrinterVisitor;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.google.common.truth.Truth;
import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.transformations.KeyJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
class KeyJavaPipelineTest {
    public KeyJavaPipeline createPipelineTest(File testFolder) throws FileNotFoundException {
        var js = new JavaService(Collections.singleton(testFolder));
        var inputFolder = new File(testFolder, "input");
        final var jp = js.createJavaParser();
        var files = inputFolder.listFiles();
        var cu = new ArrayList<CompilationUnit>();
        for (File it : Objects.requireNonNull(files)) {
            var r = jp.parse(it);
            if (!r.isSuccessful()) {
                for (Problem problem : r.getProblems()) {
                    System.out.println(problem);
                }
                throw new IllegalStateException();
            }
            var c = r.getResult().get();
            cu.add(c);
        }
        var services = new TransformationPipelineServices(js, new TransformationPipelineServices.TransformerCache(cu));
        var kjp = KeyJavaPipeline.createDefault(services);
        var kjp2 = new KeyJavaPipeline(services);
        var cnt = 0;
        for (JavaTransformer step : kjp.getSteps()) {
            kjp2.add(step);
            final var file = new File(new File(testFolder, "actual"),
                    String.format("%02d_%s", ++cnt, step.getClass().getSimpleName()));
            kjp2.add(new DebugOutputTransformer(file, services));
        }
        return kjp2;
    }

    @TestFactory
    Stream<DynamicTest> simple() throws IOException {
        return generatePipelineTests(new File("pipelineTests/simple").getAbsoluteFile());
    }

    private Stream<DynamicTest> generatePipelineTests(File testFolder) throws IOException {
        var pt = createPipelineTest(testFolder);
        pt.apply();
        var expected = new File(testFolder, "expected").toPath();
        var actual = new File(testFolder, "actual").toPath();

        return Files.walk(expected)
                .filter(Files::isRegularFile)
                .map(it ->
                        DynamicTest.dynamicTest(it.toString(), () -> checkEqualFile(it, expected, actual)));
    }

    private void checkEqualFile(Path expectedFile, Path expectedFolder, Path actualFolder) throws IOException {
        var actualFile = actualFolder.resolve(expectedFolder.relativize(expectedFile));
        if (!Files.exists(actualFile)) {
            Assertions.fail("Actual file " + actualFile + " does not exists.");
        }
        var expected = Files.readString(expectedFile);
        var actual = Files.readString(actualFile);

        Truth.assertThat(actual).isEqualTo(expected);
    }

    private static class DebugOutputTransformer extends JavaTransformer {
        final File outputFolder;
        final Set<File> alreadyWritten = new HashSet<>();
        private static final Logger LOGGER = LoggerFactory.getLogger(DebugOutputTransformer.class);
        private final Printer myPrinter = new DefaultPrettyPrinter(
                MyPrintVisitor::new,
                new DefaultPrinterConfiguration());


        public DebugOutputTransformer(File s, TransformationPipelineServices services) {
            super(services);
            outputFolder = s;
        }

        @Override
        public void apply(TypeDeclaration<?> td) {
            outputFolder.mkdirs();
            for (CompilationUnit unit : services.getCache().getUnits()) {
                var name = unit.getPrimaryTypeName().get();
                var file = new File(outputFolder, name + ".java");
                if (!alreadyWritten.contains(file)) {
                    alreadyWritten.add(file);
                    try {
                        unit.printer(myPrinter);
                        Files.writeString(file.toPath(), unit.toString());
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

        @Override
        public void visit(KeyPassiveExpression n, Void arg) {
            printer.print("@(");
            n.getExpr().accept(this, arg);
            printer.print(")");
        }
    }
}
