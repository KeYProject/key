/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.KeYJPMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.loader.JP2KeYConverter;
import de.uka.ilkd.key.java.loader.JP2KeYTypeConverter;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.util.collection.ImmutableSet;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

/**
 * @author Alexander Weigl
 * @version 1 (17.04.23)
 */
public class ReduxTest {
    public static final String PATHTOREDUX =
        "../key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux";

    private final Services services = new Services(JavaProfile.getDefaultProfile());
    private final KeYJPMapping mapping = services.getJavaService().getMapping();
    private final TypeSolver typeSolver = new JavaParserTypeSolver(Paths.get(PATHTOREDUX));
    private final JP2KeYConverter converter = new JP2KeYConverter(services, mapping,
        new Namespace<>(), new JP2KeYTypeConverter(services, typeSolver, mapping));
    private final JavaSymbolSolver javaSymbolSolver = new JavaSymbolSolver(typeSolver);

    private final JavaParser parser =
        new JavaParser(new ParserConfiguration().setSymbolResolver(javaSymbolSolver));

    public ReduxTest() {
        var sorts = services.getNamespaces().sorts();
        sorts.add(new SortImpl(new Name("int"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("boolean"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("long"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("double"), ImmutableSet.empty(), false));
        sorts.add(new SortImpl(new Name("float"), ImmutableSet.empty(), false));
        services.activateJava(null);
    }

    @Test
    void testJavaLangObject() {
        typeSolver.getSolvedJavaLangObject();
    }

    @TestFactory
    Stream<DynamicTest> testRedux() throws IOException {
        return Files.walk(Paths.get(PATHTOREDUX))
                .filter(it -> it.toString().endsWith(".java"))
                .map(it -> DynamicTest.dynamicTest(it.toString(), () -> parse(it)));
    }


    private CompilationUnit parse(Path it) {
        try {
            ParseResult<CompilationUnit> res = parser.parse(it);
            if (!res.isSuccessful()) {
                res.getProblems().forEach(System.out::println);
                Assertions.fail("Problems in file: " + it);
            }
            var r = converter.processCompilationUnit(res.getResult().get());
            System.out.println(r);
            return res.getResult().get();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
