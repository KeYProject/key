import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.DefaultPrettyPrinterVisitor;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.transformations.KeyJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
public class KeyJavaPipelineTest {
    public KeyJavaPipeline createPipelineTest(File testFolder) throws FileNotFoundException {
        var js = new JavaService(Collections.singleton(testFolder));
        var inputFolder = new File(testFolder, "input");
        final var jp = js.createJavaParser();
        var files = inputFolder.listFiles();
        var cu = new ArrayList<CompilationUnit>();
        for (File it : files) {
            var r = jp.parse(it);
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

    @Test
    void simple() throws FileNotFoundException {
        var pt = createPipelineTest(new File("pipelineTests/simple"));
        pt.apply();
    }

    private static class DebugOutputTransformer extends JavaTransformer {
        final File outputFolder;
        final Set<File> alreadyWritten = new HashSet<>();
        private static final Logger LOGGER = LoggerFactory.getLogger(DebugOutputTransformer.class);
        private Printer myPrinter = new DefaultPrettyPrinter(
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

        public MyPrintVisitor(PrinterConfiguration configuration, SourcePrinter printer) {
            super(configuration, printer);
        }

        @Override
        public void visit(KeyPassiveExpression n, Void arg) {
            printer.print("@(");
            n.getExpr().accept(this, arg);
            printer.print(")");
        }
    }
}
