package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import de.uka.ilkd.key.java.transformations.pipeline.lambda.NameGenerator;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import com.sun.tools.javac.tree.JCTree;

/**
 * Represents a replacement for a lambda expression with an inner class.
 */
public class Replacement {

    private final NormalizedLambda normalizedLambda;
    private final NameGenerator nameGenerator;
    private final Context context;
    private final Pair<JmlTree.JmlClassDecl, JCTree.JCNewClass> replacements;

    /**
     * Constructs a Replacement from a normalized lambda.
     *
     * @param normalizedLambda the normalized lambda to replace
     * @param nameGenerator the name generator for creating unique names
     * @param context the javac context
     */
    public Replacement(NormalizedLambda normalizedLambda, NameGenerator nameGenerator, Context context) {
        this.normalizedLambda = normalizedLambda;
        this.nameGenerator = nameGenerator;
        this.context = context;
        this.replacements = normalizedLambda.lambdaToInnerMethod(nameGenerator, context);
    }

    /**
     * Gets the replacement inner class definition.
     *
     * @return the JML class declaration for the inner class
     */
    public JmlTree.JmlClassDecl getReplacementInnerClass() {
        return replacements.first;
    }

    /**
     * Gets the replacement reference (new class instantiation).
     *
     * @return the new class expression
     */
    public JCTree.JCNewClass getReplacementReference() {
        return replacements.second;
    }

    /**
     * Simple pair class to hold two values.
     */
    public static class Pair<F, S> {
        public final F first;
        public final S second;

        public Pair(F first, S second) {
            this.first = first;
            this.second = second;
        }
    }
}