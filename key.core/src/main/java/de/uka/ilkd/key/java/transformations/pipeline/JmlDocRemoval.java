package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.key.JmlDocModifier;
import com.github.javaparser.ast.key.JmlDocsBodyDeclaration;
import com.github.javaparser.ast.key.JmlDocsStatements;
import com.github.javaparser.ast.key.JmlDocsTypeDeclaration;
import org.jspecify.annotations.NonNull;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class JmlDocRemoval extends JavaTransformer {
    public JmlDocRemoval(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(it -> {
            if (it instanceof Modifier m) {
                if (m.keyword() instanceof JmlDocModifier) {
                    it.remove();
                }
            }

            if (it instanceof JmlDocsStatements ||
                    it instanceof JmlDocsTypeDeclaration ||
                    it instanceof JmlDocsBodyDeclaration) {
                it.remove();
            }
        });
    }
}
