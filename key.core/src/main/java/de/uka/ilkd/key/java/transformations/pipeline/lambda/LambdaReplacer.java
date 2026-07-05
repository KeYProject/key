package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import de.uka.ilkd.key.java.ast.CompilationUnit;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import transform.NormalizedLambda;
import transform.Replacement;

import java.util.ArrayList;
import java.util.List;

public class LambdaReplacer implements JavaTransformer {
    private final List<ClassDeclaration> exportedDeclarations = new ArrayList<>();
    private final NameGenerator nameGenerator;
    private final CompilationUnit compilationUnit;

    public LambdaReplacer(CompilationUnit compilationUnit, NameGenerator nameGenerator) {
        this.compilationUnit = compilationUnit;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public void apply(com.github.javaparser.ast.CompilationUnit cu) {
        JavaTransformer.super.apply(cu);
    }

    @Override
    public JCTree translate(JCTree tree) {
        if (tree instanceof JCTree.JCLambda) {
            JCTree.JCLambda lambda = (JCTree.JCLambda) tree;

            // Replaces other Lambdas in Lambda's Body
            LambdaReplacer lambdaBodyReplacer = new LambdaReplacer(context, compilationUnit);
            lambda.body = lambdaBodyReplacer.translate(lambda.body);
            //TODO: api.typecheck() generated program. Does not seem to help?

            NormalizedLambda normalizedLambda = new NormalizedLambda(lambda, nameGenerator, context);
            Replacement lambdaReplacement = new Replacement(normalizedLambda, nameGenerator, context);
            exportedDeclarations.add(lambdaReplacement.getReplacementInnerClass());
            exportedDeclarations.addAll(lambdaBodyReplacer.getExportedDeclarations());
            return lambdaReplacement.getReplacementReference();
        }
        return super.translate(tree);
    }

    public List<JCTree.JCClassDecl> getExportedDeclarations() {
        return exportedDeclarations;
    }
}
