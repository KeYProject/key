/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.loader.JP2KeYConverter;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableSet;

/**
 * @author Alexander Weigl
 * @version 1 (08.03.22)
 */
class TranslationTest {
    private static Services services = new Services(JavaProfile.getDefaultProfile());
    private static JP2KeYConverter converter;

    @BeforeAll
    static void setup() {
        var sorts = services.getNamespaces().sorts();
        sorts.add(new SortImpl(new Name("int"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("boolean"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("long"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("double"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("float"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("Seq"), ImmutableSet.empty(), false));
        services.activateJava(null);
        converter = services.getJavaService().getConverter(null);
        services.getJavaService().parseSpecialClasses();

    }

    //private final KeYJPMapping mapping = services.getJavaService().getMapping();
    // private final TypeSolver typeSolver = new ReflectionTypeSolver(true);
    //private final TypeSolver typeSolver = new JavaParserTypeSolver(ReduxTest.PATHTOREDUX);
    //private final JP2KeYConverter converter = new JP2KeYConverter(services, mapping,
    //    new Namespace<>(), new JP2KeYTypeConverter(services, typeSolver, mapping));

    private final CompilationUnit cu =
            StaticJavaParser.parse("public class A { Object a; String s; {} }");
    //private final JavaSymbolSolver javaSymbolSolver = new JavaSymbolSolver(typeSolver);
    private final Node parent;

    public TranslationTest() {
        System.out.println("TranslationTest.TranslationTest");
        services.getJavaInfo().getJavaLangObject();
        parent = cu.getType(0).getMember(2);// Initializer
    }

    @ParameterizedTest
    @CsvFileSource(resources = "/javaExprs.txt", delimiter = '°')
    void expressions(String javaExpr) {
        Assumptions.assumeFalse(javaExpr.isBlank());
        var expr = StaticJavaParser.parseExpression(javaExpr);
        expr.setParentNode(parent);
        var converted = converter.process(expr);
        Assertions.assertNotEquals(null, converted);
        Assertions.assertInstanceOf(Expression.class, converted,
                "Unexpected type: " + converted.getClass());
        System.out.println(converted);
    }
}
