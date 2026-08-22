package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import analyzer.FreeVariablesLocator;
import com.github.javaparser.ast.expr.LambdaExpr;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.NameGenerator;

import java.util.Set;

/**
 * Represents a lambda expression with its free variables.
 */
public class TLambda {
    protected final LambdaExpr lambda;
    protected final NameGenerator nameGenerator;

    public Set<Symbol> getFreeVariables() {
        return new FreeVariablesLocator(context).extractFreeVariables(lambda);
    }
}