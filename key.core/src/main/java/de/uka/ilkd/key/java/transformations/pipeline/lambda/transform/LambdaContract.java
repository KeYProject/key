package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;

/**
 * Represents a lambda expression with its associated JML contract specifications.
 */
public class LambdaContract {

    private final NormalizedLambda normalizedLambda;
    private final JCTree.JCMethodDecl lambdaReplacementMethod;
    private final Context context;
    private final List<JmlTree.JmlSpecificationCase> lambdaContract;
    private final JmlTree.Maker maker;

    /**
     * Constructs a LambdaContract from a normalized lambda and its replacement method.
     *
     * @param normalizedLambda the normalized lambda expression
     * @param lambdaReplacementMethod the method declaration that replaces the lambda
     * @param context the javac context
     */
    public LambdaContract(NormalizedLambda normalizedLambda,
                          JCTree.JCMethodDecl lambdaReplacementMethod,
                          Context context) {
        this.normalizedLambda = normalizedLambda;
        this.lambdaReplacementMethod = lambdaReplacementMethod;
        this.context = context;
        this.maker = JmlTree.Maker.instance(context);
        this.lambdaContract = extractSpec();
    }

    /**
     * Converts the lambda contract clauses to model method declarations.
     *
     * @return a list of JML method declarations representing the contract as model methods
     */
    public List<JmlTree.JmlMethodDecl> toModelMethods() {
        if (lambdaContract.isEmpty()) {
            return List.nil();
        }

        // Process only the first specification case (matching Kotlin implementation)
        JmlTree.JmlSpecificationCase specCase = lambdaContract.head;
        List<JmlTree.JmlMethodDecl> result = List.nil();
        for (JmlTree.JmlMethodClause clause : specCase.clauses) {
            JmlTree.JmlMethodDecl translated;
            switch (clause.token) {
                case REQUIRES:
                    translated = translateRequires(clause);
                    break;
                case ENSURES:
                    translated = translateEnsures(clause);
                    break;
                default:
                    throw new UnsupportedOperationException("Unsupported clause type: " + clause.token);
            }
            result = result.append(translated);
        }
        return List.from(result);
    }

    /**
     * Translates an ENSURES clause to a model method.
     *
     * @param clause the ENSURES clause to translate
     * @return a JML method declaration representing the ensures condition
     */
    private JmlTree.JmlMethodDecl translateEnsures(JmlTree.JmlMethodClause clause) {
        Name name = maker.Name("postConditionMethod");
        System.out.println("Found clause ");
        System.out.print(clause);

        if (clause instanceof JmlTree.JmlMethodClauseExpr) {
            JmlTree.JmlMethodClauseExpr exprClause = (JmlTree.JmlMethodClauseExpr) clause;
            Symbol.VarSymbol resultSymbol = new Symbol.VarSymbol(
                0,
                maker.Name("__result"),
                normalizedLambda.lambdaReturnType(),
                null
            );
            List<JCTree.JCVariableDecl> extraParams = List.of(maker.VarDef(resultSymbol, null));
            return modelMethod(exprClause.expression, name, extraParams);
        }
        throw new UnsupportedOperationException("Unsupported ensures clause: " + clause.toString());
    }

    /**
     * Translates a REQUIRES clause to a model method.
     *
     * @param clause the REQUIRES clause to translate
     * @return a JML method declaration representing the requires condition
     */
    private JmlTree.JmlMethodDecl translateRequires(JmlTree.JmlMethodClause clause) {
        Name name = maker.Name("preConditionMethod");
        System.out.println("Found clause ");
        System.out.print(clause);

        if (clause instanceof JmlTree.JmlMethodClauseExpr) {
            JmlTree.JmlMethodClauseExpr exprClause = (JmlTree.JmlMethodClauseExpr) clause;
            return modelMethod(exprClause.expression, name, List.nil());
        }
        throw new UnsupportedOperationException("Unsupported requires clause: " + clause.toString());
    }

    /**
     * Creates a model method from an expression.
     *
     * @param expression the expression to use in the method body
     * @param methodName the name of the method
     * @param extraParams additional parameters for the method
     * @return a JML method declaration
     */
    private JmlTree.JmlMethodDecl modelMethod(JCTree.JCExpression expression,
                                               Name methodName,
                                               List<JCTree.JCVariableDecl> extraParams) {
        Utils utils = Utils.instance(context);

        JmlTree.JmlAnnotation annotation = utils.tokenToAnnotationAST(
            JmlTokenKind.MODEL,
            expression.startPosition,
            expression.startPosition
        );
        JmlTree.JmlModifiers mods = maker.Modifiers(0, List.of(annotation));

        Symtab symtab = Symtab.instance(context);
        JCTree.JCExpression restype = maker.Type(symtab.booleanType);

        return maker.MethodDef(
            mods,
            methodName,
            restype,
            lambdaReplacementMethod.typarams,
            null,
            lambdaReplacementMethod.params.appendList(extraParams),
            List.nil(),
            maker.Block(0, List.of(maker.Return(expression))),
            null
        );
    }

    /**
     * Extracts the JML specification from the lambda expression.
     *
     * @return a list of JML specification cases found in the lambda
     */
    private List<JmlTree.JmlSpecificationCase> extractSpec() {
        LambdaContractExtractor extractor = new LambdaContractExtractor();

        normalizedLambda.lambda.accept(extractor);
        return extractor.spec != null ? extractor.spec : List.nil();
    }
}