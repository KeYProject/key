package de.uka.ilkd.key.java.transformations;

import java.util.List;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.Expression;
import jdk.jshell.JShell;
import jdk.jshell.SnippetEvent;

/**
 * An evaluator for constant expression based on {@link JShell}.
 *
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
// TODO weigl: We want to rewrite this into a more isolated non-JShell version. JShell performance
// is not tested.
public class ConstantExpressionEvaluator {
    private final JShell jShell = JShell.create();

    public boolean isCompileTimeConstant(Expression expr) throws EvaluationException {
        List<SnippetEvent> value = jShell.eval(expr.toString());
        assert value.size() == 1;
        SnippetEvent evt = value.get(0);
        // throw new EvaluationException("Could not evaluate " + expr, evt.exception());
        return evt.exception() == null;
        // String result = evt.value();
    }

    public Expression evaluate(Expression expression) throws EvaluationException {
        return evaluate(expression.toString());
    }

    public Expression evaluate(String expression) throws EvaluationException {
        List<SnippetEvent> value = jShell.eval(expression);
        assert value.size() == 1;
        SnippetEvent evt = value.get(0);

        if (evt.exception() != null) {
            throw new EvaluationException("Could not evaluate " + expression, evt.exception());
        }

        try {
            // weigl: use the static java parser; special feature (KeY or JML syntax) are not
            // expected in the output of JShell
            return StaticJavaParser.parseExpression(evt.value());
        } catch (ParseProblemException e) {
            throw new EvaluationException("Could not evaluate " + expression, e);
        }

    }
}
