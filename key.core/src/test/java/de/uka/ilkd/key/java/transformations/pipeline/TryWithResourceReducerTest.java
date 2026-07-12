package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.07.26)
 */
class TryWithResourceReducerTest {
    @Test
    void test() {
        String source = """
                class Demo {
                    void run() {
                        try (Resource r1 = new Resource1(); Resource r2 = new Resource2()) {
                            r1.use();
                            r2.use();
                        } catch (Exception e) {
                            System.out.println("caught: " + e);
                        } finally {
                            System.out.println("done");
                        }
                    }
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new TryWithResourceReducer();
        t.apply(cu);
        System.out.println(cu);
    }
}