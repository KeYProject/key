import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JP2KeyConverter;
import de.uka.ilkd.key.java.KeyJPMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;

/**
 * @author Alexander Weigl
 * @version 1 (08.03.22)
 */
class TranslationTest {
    private final JP2KeyConverter converter = new JP2KeyConverter(new Services(JavaProfile.getDefaultProfile()),
            new KeyJPMapping(), new Namespace<>());

    private final CompilationUnit cu
            = StaticJavaParser.parse("public class A { Object a; String s; {} }");
    private final JavaSymbolSolver javaSymbolSolver = new JavaSymbolSolver(new ReflectionTypeSolver(true));
    private final Node parent;

    public TranslationTest() {
        javaSymbolSolver.inject(cu);
        parent = cu.getType(0).getMember(2);//Initializer
    }

    @ParameterizedTest
    @CsvFileSource(resources = "/javaExprs.txt", delimiter = '°')
    void expressions(String javaExpr) {
        Assumptions.assumeFalse(javaExpr.isBlank());
        var expr = StaticJavaParser.parseExpression(javaExpr);
        expr.setParentNode(parent);
        var converted = converter.process(expr);
        Assertions.assertNotEquals(null, converted);
        Assertions.assertTrue(converted instanceof Expression, "Unexpected type: " + converted.getClass());
        System.out.println(converted);
    }
}
