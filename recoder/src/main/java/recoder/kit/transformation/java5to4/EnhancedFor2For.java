/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.java.Expression;
import recoder.java.LoopInitializer;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.statement.EnhancedFor;
import recoder.java.statement.For;
import recoder.java.statement.LabeledStatement;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * converts an enhanced for loop to an "old style" for loop. This follows JLS 3rd edition, �14.14.2.
 * <p>
 * Currently, if given enhanced for iterates over an array, this will replace the enhanced for with
 * a statement block and not inline it into a possibly given statement block, yielding possibly not
 * nicely formatted (but fully functional) code.
 *
 * @author Tobias Gutzmann
 * @since 0.80
 */
public final class EnhancedFor2For extends TwoPassTransformation {
    private final CrossReferenceServiceConfiguration sc;
    private final EnhancedFor enhancedFor;
    private String iteratorName;
    private String arrayReferenceName;
    private Type guardType;
    private Type iteratorType;

    /**
     * creates a new transformation. Note that if neither specifying iteratorName and
     * arrayReferenceName, this transformation will always work.
     *
     * @param sc cross reference source configuration
     * @param enhancedFor the EnhancedFor to be replaced
     * @param iteratorName name for the iterator/int. if <code>null</code>, will find one
     *        automatically.
     * @param arrayReferenceName name for the array reference (if neccessary). if <code>null</code>,
     *        will find one automatically.
     */
    public EnhancedFor2For(CrossReferenceServiceConfiguration sc, EnhancedFor enhancedFor,
            String iteratorName, String arrayReferenceName) {
        super(sc);
        this.sc = sc;
        this.enhancedFor = enhancedFor;
        this.iteratorName = iteratorName;
        this.arrayReferenceName = arrayReferenceName;
    }

    /**
     * calls <code>EnhancedFor2For(sc, enhancedFor, null, null)</code>
     *
     * @param sc
     * @param enhancedFor
     */
    public EnhancedFor2For(CrossReferenceServiceConfiguration sc, EnhancedFor enhancedFor) {
        this(sc, enhancedFor, null, null);
    }

    @Override
    public ProblemReport analyze() {
        if (iteratorName != null) {
            Variable v = sc.getSourceInfo().getVariable(iteratorName, enhancedFor.getASTParent());
            if (v != null) {
                return setProblemReport(new NameConflict(v));
            }
        } else {
            // iteratorName = "i";
            // int i = 0;
            // while( sc.getSourceInfo().getVariable(iteratorName, enhancedFor) != null) {
            // iteratorName = "i" + ++i;
            // }
            iteratorName = VariableKit.createValidVariableName(sc.getSourceInfo(),
                enhancedFor.getASTParent(), "i");
        }
        if (arrayReferenceName != null) {
            Variable v =
                sc.getSourceInfo().getVariable(arrayReferenceName, enhancedFor.getASTParent());
            if (v != null) {
                return setProblemReport(new NameConflict(v));
            }
        } else {
            arrayReferenceName = VariableKit.createValidVariableName(sc.getSourceInfo(),
                enhancedFor.getASTParent(), "a");
        }
        guardType = sc.getSourceInfo().getType(enhancedFor.getGuard());
        if (guardType instanceof ClassType) {
            MethodReference mr =
                getProgramFactory().createMethodReference((ReferencePrefix) enhancedFor.getGuard(),
                    getProgramFactory().createIdentifier("iterator"));
            mr.setExpressionContainer(enhancedFor);
            iteratorType = sc.getSourceInfo().getType(mr);
        } else if (guardType instanceof ArrayType) {
            iteratorType = null;
        } else {
            throw new IllegalStateException("Broken Model");
        }
        return setProblemReport(EQUIVALENCE);
    }

    @Override
    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();

        LoopInitializer init;
        Expression guard;
        ASTList<Expression> update;
        LocalVariableDeclaration firstStmnt;
        // common part, initializer is set independently afterwards:
        firstStmnt =
            (((LocalVariableDeclaration) enhancedFor.getInitializers().get(0)).deepClone());

        if (iteratorType == null) {
            // array type
            init = pf.createLocalVariableDeclaration(null, TypeKit.createTypeReference(pf, "int"),
                pf.createIdentifier(iteratorName), pf.createIntLiteral(0));
            guard = pf.createLessThan(pf.createVariableReference(pf.createIdentifier(iteratorName)),
                pf.createArrayLengthReference(
                    pf.createVariableReference(pf.createIdentifier(arrayReferenceName))));
            update = new ASTArrayList<>(pf.createPostIncrement(
                pf.createVariableReference(pf.createIdentifier(iteratorName))));
            firstStmnt.getVariableSpecifications().get(0)
                    .setInitializer(pf.createArrayReference(
                        pf.createVariableReference(pf.createIdentifier(arrayReferenceName)),
                        new ASTArrayList<>(
                            pf.createVariableReference(pf.createIdentifier(iteratorName)))));
        } else {
            // Iterable
            init = pf.createLocalVariableDeclaration(null,
                TypeKit.createTypeReference(pf, iteratorType, true),
                pf.createIdentifier(iteratorName),
                pf.createMethodReference(
                    (ReferencePrefix) enhancedFor.getExpressionAt(0).deepClone(),
                    pf.createIdentifier("iterator")));
            guard = pf.createMethodReference(
                pf.createVariableReference(pf.createIdentifier(iteratorName)),
                pf.createIdentifier("hasNext"));
            update = null;
            firstStmnt.getVariableSpecifications().get(0)
                    .setInitializer(pf.createMethodReference(
                        pf.createVariableReference(pf.createIdentifier(iteratorName)),
                        pf.createIdentifier("next")));
        }

        ASTList<Statement> statements = new ASTArrayList<>(2);

        statements.add(firstStmnt);
        if (enhancedFor.getStatementCount() > 0) {
            // if statement block, go into it
            Statement s = enhancedFor.getStatementAt(0);
            if (s instanceof StatementBlock) {
                StatementBlock sb = (StatementBlock) s;
                for (int i = 0; i < sb.getStatementCount(); i++) {
                    statements.add(sb.getStatementAt(i).deepClone());
                }
            } else {
                statements.add(s.deepClone());
            }
        }

        For newFor = new For(new ASTArrayList<>(init), guard, update,
            new StatementBlock(statements));
        newFor.makeAllParentRolesValid();

        Statement replacement;
        Statement replacee;

        if (iteratorType == null) {
            ASTArrayList<Statement> sml = new ASTArrayList<>(2);
            // create array name reference
            LocalVariableDeclaration lvd =
                pf.createLocalVariableDeclaration(null, TypeKit.createTypeReference(pf, guardType),
                    pf.createIdentifier(arrayReferenceName), enhancedFor.getGuard().deepClone());
            sml.add(lvd);

            // clone labels
            Statement s;
            s = newFor;
            replacee = enhancedFor;
            while (replacee.getASTParent() instanceof LabeledStatement) {
                replacee = (LabeledStatement) replacee.getASTParent();
                s = new LabeledStatement(((LabeledStatement) replacee).getIdentifier().deepClone(),
                    s);
            }
            sml.add(s);
            replacement = pf.createStatementBlock(sml);
        } else {
            replacement = newFor;
            replacee = enhancedFor;
        }
        replace(replacee, replacement);
    }
}
