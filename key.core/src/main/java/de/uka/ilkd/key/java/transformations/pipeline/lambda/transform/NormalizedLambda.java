package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.IdentifierToFieldAccessNormalizer;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.NameGenerator;
import org.jmlspecs.openjml.JmlTree;

/**
 * Represents a normalized lambda expression with methods to convert it to an inner class.
 */
public class NormalizedLambda extends TLambda {

    private final JCTree.JCLambda lambdaToNormalize;

    /**
     * Constructs a NormalizedLambda from a lambda expression.
     *
     * @param lambdaToNormalize the lambda to normalize
     * @param nameGenerator the name generator for creating unique names
     * @param context the javac context
     */
    public NormalizedLambda(JCTree.JCLambda lambdaToNormalize, NameGenerator nameGenerator, Context context) {
        super(normalizeLambda(lambdaToNormalize, context, nameGenerator), nameGenerator, context);
        this.lambdaToNormalize = lambdaToNormalize;
    }

    /**
     * Gets the return type of the lambda expression.
     *
     * @return the return type of the lambda's functional interface method
     */
    public Type lambdaReturnType() {
        return ((Type.MethodType) lambdaToNormalize.type.tsym.members().elems.sym.type).restype;
        // TODO generate body-type for lambda and use that instead
        // return lambdaToNormalize.body.type;
    }

    /**
     * Converts the lambda to an inner class definition and a new class instantiation.
     *
     * @param nameGenerator the name generator for creating unique names
     * @param context the javac context
     * @return a pair containing the inner class definition and the new class expression
     */
    public Replacement.Pair<JmlTree.JmlClassDecl, JCTree.JCNewClass> lambdaToInnerMethod(
            NameGenerator nameGenerator, Context context) {

        Name name = (lambda.type.tsym.name == null)
                ? nameGenerator.generate("Lambda", lambda.startPosition)
                : nameGenerator.generate(lambda.type.tsym.name.toString(), lambda.startPosition);

        JmlTree.Maker maker = JmlTree.Maker.instance(context);
        IdentifierToFieldAccessNormalizer lambdaNormalizer = new IdentifierToFieldAccessNormalizer(maker);
        JCTree.JCLambda normalizedLambda = (JCTree.JCLambda) lambdaNormalizer.translate(lambda);
        TLambda normalizedLambdaInfo = new TLambda(normalizedLambda, nameGenerator, context);

        return new Replacement.Pair<>(
                innerClassDefinition(name),
                maker.NewClass(
                        null,
                        List.nil(),
                        maker.Ident(name),
                        List.from(normalizedLambdaInfo.getFreeVariables().stream()
                                .map(it -> maker.Ident(it.name))
                                .collect(List.collector())),
                        null
                )
        );
    }

    /**
     * Creates the inner class definition for the lambda.
     *
     * @param name the name for the inner class
     * @return the JML class declaration
     */
    private JmlTree.JmlClassDecl innerClassDefinition(Name name) {
        JmlTree.Maker maker = JmlTree.Maker.instance(context);

        Symbol.MethodSymbol methodSymbol = findAbstractMethodSymbol();
        Symbol.MethodSymbol definedMethodSymbol = new Symbol.MethodSymbol(
                Flags.PUBLIC,
                methodSymbol.name,
                methodSymbol.type,
                methodSymbol.owner
        );
        definedMethodSymbol.params = List.from(
                methodSymbol.params.stream()
                        .map(it -> new Symbol.VarSymbol(
                                it.flags(),
                                lambda.params.get(methodSymbol.params.indexOf(it)).name,
                                it.type,
                                it.owner
                        ))
                        .collect(List.collector())
        );

        JCTree body = lambda.body;
        JmlTree.JmlClassDecl clazz = maker.ClassDef(
                maker.Modifiers(Flags.PUBLIC | Flags.FINAL | Flags.STATIC),
                name,
                List.nil(),
                null,
                List.of(maker.Ident(lambda.type.tsym.name)),
                List.nil()
        );

        Name thisReplacement = maker.Name("outer_this");
        Name superReplacement = maker.Name("outer_super");
        JCTree.JCMethodDecl classConstructor = createInnerConstructor(
                name, clazz, thisReplacement, superReplacement);
        JCTree.JCMethodDecl lambdaMethod = createLambdaMethod(
                maker, definedMethodSymbol, body, thisReplacement, superReplacement);
        List<JmlTree.JmlMethodDecl> modelMethods =
                new LambdaContract(this, (JCTree.JCMethodDecl) lambdaMethod, context).toModelMethods();

        List<JCTree.JCVariableDecl> pseudoClosure = List.from(getFreeVariables().stream()
                .map(it -> {
                    Name fieldName = (it.name.equals(maker.Name("this"))) ? thisReplacement : it.name;
                    if (it instanceof Symbol.VarSymbol) {
                        Symbol.VarSymbol varSym = (Symbol.VarSymbol) it;
                        return maker.VarDef(
                                maker.Modifiers(Flags.PRIVATE | Flags.FINAL),
                                fieldName,
                                maker.Type(varSym.type),
                                null
                        );
                    } else if (it instanceof Symtab) {
                        Symtab symtab = (Symtab) it;
                        System.out.println(symtab);
                        return maker.VarDef(symtab.lengthVar, null);
                    } else {
                        throw new UnsupportedOperationException(it.toString());
                    }
                })
                .collect(List.collector()));

        clazz.defs = List.from(pseudoClosure.appendList(modelMethods).append(lambdaMethod).append(classConstructor));
        return clazz;
    }

    /**
     * Finds the abstract method symbol from the lambda's functional interface.
     *
     * @return the method symbol for the functional interface method
     */
    private Symbol.MethodSymbol findAbstractMethodSymbol() {
        return (Symbol.MethodSymbol) lambda.type.tsym.members().elements.stream()
                .filter(it -> {
                    long flags = Flags.asFlagSet(it.flags());
                    return it instanceof Symbol.MethodSymbol
                            && (flags & Flags.ABSTRACT) != 0
                            && (flags & Flags.SYNTHETIC) == 0
                            && (flags & Flags.DEFAULT) == 0;
                })
                .findFirst()
                .orElseThrow(() -> new IllegalStateException("No abstract method found in functional interface"));
    }

    /**
     * Creates the lambda method inside the inner class.
     *
     * @param maker the tree maker
     * @param definedMethodSymbol the method symbol for the generated method
     * @param body the lambda body
     * @param thisReplacement replacement name for "this"
     * @param superReplacement replacement name for "super"
     * @return the method declaration
     */
    private JCTree.JCMethodDecl createLambdaMethod(
            JmlTree.Maker maker,
            Symbol.MethodSymbol definedMethodSymbol,
            JCTree body,
            Name thisReplacement,
            Name superReplacement) {

        RenameVariable thisSanitizer = new RenameVariable(
                maker.Name("this"), context, name -> thisReplacement);
        RenameVariable superSanitizer = new RenameVariable(
                maker.Name("super"), context, name -> superReplacement);

        JCTree sanitizedBody = thisSanitizer.translate(superSanitizer.translate(body));

        JCTree.JCStatement bodyStatement = (body instanceof JCTree.JCExpression)
                ? maker.Return((JCTree.JCExpression) sanitizedBody)
                : (JCTree.JCStatement) sanitizedBody;

        return maker.MethodDef(
                definedMethodSymbol,
                maker.Block(0, List.of(bodyStatement))
        );
    }

    /**
     * Creates the constructor for the inner class.
     *
     * @param name the class name
     * @param clazz the class declaration
     * @param thisNameReplacement replacement name for "this"
     * @param superNameReplacement replacement name for "super"
     * @return the constructor declaration
     */
    private JCTree.JCMethodDecl createInnerConstructor(
            Name name,
            JmlTree.JmlClassDecl clazz,
            Name thisNameReplacement,
            Name superNameReplacement) {

        JmlTree.Maker maker = JmlTree.Maker.instance(context);
        TreeMaker jcMaker = TreeMaker.instance(context);

        Symbol.MethodSymbol constructorSymbol = new Symbol.MethodSymbol(
                Flags.PUBLIC, name, Type.JCVoidType(), clazz.thisSymbol);

        List<JCTree.JCStatement> assignments = List.from(getFreeVariables().stream()
                .map(it -> {
                    Name assignmentName = sanitizeName(maker, it.name, thisNameReplacement, superNameReplacement);
                    return jcMaker.Exec(
                            maker.Assign(
                                    maker.QualIdent("this", assignmentName.toString()),
                                    maker.Ident(assignmentName)
                            )
                    );
                })
                .collect(List.collector()));

        JCTree.JCMethodDecl ctor = maker.MethodDef(
                constructorSymbol,
                maker.Block(0, assignments)
        );

        ctor.params = List.from(getFreeVariables().stream()
                .map(it -> {
                    Name argumentName = sanitizeName(maker, it.name, thisNameReplacement, superNameReplacement);
                    return maker.VarDef(
                            maker.Modifiers(0),
                            argumentName,
                            maker.Type(it.type),
                            null
                    );
                })
                .collect(List.collector()));

        return ctor;
    }

    /**
     * Sanitizes a name by replacing special names like "this" and "super".
     *
     * @param maker the tree maker
     * @param name the original name
     * @param thisReplacementName replacement for "this"
     * @param superReplacementName replacement for "super"
     * @return the sanitized name
     */
    private static Name sanitizeName(
            JmlTree.Maker maker,
            Name name,
            Name thisReplacementName,
            Name superReplacementName) {

        if (name.equals(maker.Name("this"))) {
            return thisReplacementName;
        } else if (name.equals(maker.Name("super"))) {
            return superReplacementName;
        } else {
            return name;
        }
    }

    /**
     * Normalizes a lambda expression by converting identifier accesses to field accesses.
     *
     * @param lambda the lambda to normalize
     * @param context the javac context
     * @param nameGenerator the name generator
     * @return the normalized lambda
     */
    public static JCTree.JCLambda normalizeLambda(
            JCTree.JCLambda lambda,
            Context context,
            NameGenerator nameGenerator) {

        JmlTree.Maker maker = JmlTree.Maker.instance(context);
        IdentifierToFieldAccessNormalizer lambdaNormalizer = new IdentifierToFieldAccessNormalizer(maker);
        return (JCTree.JCLambda) lambdaNormalizer.translate(lambda);
    }
}