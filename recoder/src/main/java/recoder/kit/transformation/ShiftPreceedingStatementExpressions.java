/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.*;
import recoder.service.SourceInfo;
import recoder.util.Debug;

/**
 * Transformation that ensures that the given expression is evaluated first during execution of the
 * resulting statement, while preserving the behavior. The method changes all statement expressions
 * (which might have side-effects) that are evaluated before the given expression into
 * initializations of temporary variables. These will preceed the statement the given expression is
 * located within. If the expression is contained in a statement, a statement block is inserted if
 * needed. If the expression is part of a field initializer, a new class initializer with
 * appropriate modifier executing the initialization code is inserted before the field. <BR>
 * Example:
 *
 * <PRE>
 * <p>
 * int x = f(g());
 *
 * </PRE>
 * <p>
 * becomes
 *
 * <PRE>
 * <p>
 * double d = g(); int x = f(d);
 *
 * </PRE>
 * <p>
 * or, if <CODE>x</CODE> is a field:
 *
 * <PRE>
 * {
 *     double d = g();
 *     x = f(d);
 * }
 * int x;
 *
 * </PRE>
 *
 * <DL>
 * <DT>Added:
 * <DD>If the expression was in a field initializer, a new class or object initializer block is
 * added. Otherwise, if the expression is in a statement that cannot be prepended by variable
 * declarations and has preceeding expressions with side-effects, the statement is embedded in a new
 * statement block by {@link recoder.kit.transformation.PrepareStatementList}. Afterwards, or if
 * this has not been necessary, a new temporary variable declaration is added as statement in front
 * of the containing statement, and a new variable reference replaces the old expressions.
 * <DT>Removed:
 * <DD>If the expression was in a field initializer, the initializer is cloned and replaced (the
 * clone becomes a copy assignment within the new initializer block). Otherwise, the parent
 * statement contained in a statement container might be cloned and embedded in a statement block.
 * All preceeding expressions with possible side-effects are cloned and replaced by new variable
 * references (the clones become initializers of the variable declarations).
 * </DL>
 *
 * @author AL
 */
public class ShiftPreceedingStatementExpressions extends TwoPassTransformation {

    /**
     * The expression to be brought to top-level.
     */
    private final Expression expression;

    /**
     * Expressions that preceed the input expression; later on only the ones with side-effects
     * (statement expressions).
     */
    private List<Expression> preceeding;

    /**
     * The temporary variable declarations to be inserted. They will contain clones of the
     * preceeding expressions.
     */
    private List<Statement> tempVarDecls;

    /**
     * The references to the new temporary variables to replace the preceeding expressions.
     */
    private List<VariableReference> tempVarRefs;

    /**
     * The top-level statement or field specification the expression is part of.
     */
    private NonTerminalProgramElement parent;

    /**
     * Utility transformation to make room for the temporary variables.
     */
    private PrepareStatementList preparer;

    /**
     * The new parent of the expression; the old parent if it was a statement, or a copy assignment
     * if it was a field specification - the initialization must move to the initializer block.
     */
    private Statement newParent;

    /**
     * Creates a new transformation object that shifts statement expressions to initializers of new
     * local variables.
     *
     * @param sc the service configuration to use.
     * @param x the expression that shall be accessed first in its statement or initializer.
     */
    public ShiftPreceedingStatementExpressions(CrossReferenceServiceConfiguration sc,
            Expression x) {
        super(sc);
        if (x == null) {
            throw new IllegalArgumentException("Missing expression");
        }
        this.expression = x;
    }

    /**
     * Finds out which expressions have to be shifted and their types, creates new temporary
     * variable declarations with new names, replacement references, and prepares the parent for
     * insertion unless it happens to be a field specification.
     *
     * @return the problem report, may be {@link recoder.kit.Transformation#IDENTITY}, or
     *         {@link recoder.kit.Transformation#EQUIVALENCE}.
     */
    public ProblemReport analyze() {
        // get all expressions that are executed before x
        preceeding = ExpressionKit.collectPreceedingExpressions(expression);
        // retain only expressions that might have side-effects
        int exSize = preceeding.size();
        for (int i = exSize - 1; i >= 0; i -= 1) {
            if (!ExpressionKit.containsStatements(preceeding.get(i))) {
                preceeding.remove(i);
            }
        }
        if ((expression instanceof Statement)
                && ((Statement) expression).getStatementContainer() != null) {
            parent = (NonTerminalProgramElement) expression;
        } else {
            for (ProgramElement pe = expression; pe != null; pe = parent) {
                parent = pe.getASTParent();
                if (parent instanceof Statement) {
                    if (((Statement) parent).getStatementContainer() != null) {
                        break;
                    }
                }
                if (parent instanceof FieldSpecification) {
                    break;
                }
            }
        }
        /*
         * if (parent instanceof LocalVariableDeclaration && parent.getASTParent() instanceof
         * recoder.java.statement.For) { parent = parent.getASTParent(); }
         */
        exSize = preceeding.size();
        if (exSize == 0 && (parent instanceof Statement)) {
            return setProblemReport(IDENTITY);
        }
        // a field spec as parent has a side effect (implicit assignment!)
        ProgramFactory f = getProgramFactory();
        SourceInfo si = getSourceInfo();
        if (exSize > 0) {
            Type[] exTypes = new Type[exSize];
            for (int i = 0; i < exSize; i += 1) {
                Expression ex = preceeding.get(i);
                exTypes[i] = si.getType(ex);
            }
            String[] varNames = VariableKit.getNewVariableNames(si, exTypes, expression);
            tempVarDecls = new ArrayList<>(exSize);
            tempVarRefs = new ArrayList<>(exSize);

            for (int i = 0; i < exSize; i += 1) {
                // create local temporary variable declarations for remaining
                // preceeding
                Type t = exTypes[i];
                TypeReference minTypeRef = TypeKit.createTypeReference(si, t, expression);
                String varName = varNames[i];
                LocalVariableDeclaration vdecl =
                    f.createLocalVariableDeclaration(minTypeRef, f.createIdentifier(varName));
                VariableSpecification vspec = vdecl.getVariables().get(0);
                doAttach(preceeding.get(i).deepClone(), vspec);
                // vdecl.makeAllParentRolesValid();
                tempVarDecls.add(vdecl);

                // schedule replacement expressions
                VariableReference vref = f.createVariableReference(f.createIdentifier(varName));
                vref.makeAllParentRolesValid();
                tempVarRefs.add(vref);
            }
        }
        if (parent instanceof Statement) {
            preparer = new PrepareStatementList(getServiceConfiguration(), (Statement) parent,
                isVisible());
            ProblemReport report = preparer.analyze();
            if (report instanceof Problem) {
                return setProblemReport(report);
            }
        }
        return setProblemReport(EQUIVALENCE);
    }

    /**
     * @throws IllegalStateException if the analyzation has not been called.
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        if (parent instanceof Statement) {
            newParent = (Statement) parent;
        }
        int exSize = preceeding.size();
        if (exSize == 0) {
            return;
        }
        int tempSize = tempVarDecls.size();
        // get destination statement list and position to insert into
        if (parent instanceof Statement) {
            preparer.transform();
            List<Statement> destination = preparer.getStatementList();
            parent = (NonTerminalProgramElement) preparer.getStatement();
            int destIndex;
            for (destIndex = 0; destination.get(destIndex) != parent; destIndex += 1) {
                // logic contained in loop control
            }
            // insert variable declarations into statement block
            for (Statement child : tempVarDecls) {
                destination.add(destIndex, child);
                child.setStatementContainer(((Statement) parent).getStatementContainer());
                if (isVisible()) {
                    getChangeHistory().attached(child);
                }
            }
            // replace expressions by references to local variables
            for (int i = 0; i < exSize; i += 1) {
                // Debug.log(">>> Replacing " +
                // Format.toString(Formats.ELEMENT_LONG_LOCAL,
                // preceeding.getExpression(i)) + " by " +
                // Format.toString(Formats.ELEMENT_LONG_LOCAL,
                // tempVarRefs.getVariableReference(i)) + " in " +
                // Format.toString(Formats.ELEMENT_LONG,
                // preceeding.getExpression(i).getASTParent()));
                replace(preceeding.get(i), tempVarRefs.get(i));
            }
        } else if (parent instanceof FieldSpecification) {
            ProgramFactory f = getProgramFactory();
            // create class initializer and insert it before the field
            FieldSpecification fs = (FieldSpecification) parent;
            StatementBlock body = f.createStatementBlock();
            // add variable declarations
            for (int i = 0; i < tempSize; i += 1) {
                doAttach(tempVarDecls.get(i), body, i);
            }
            // shift field specification initializer to the new block
            Expression init = fs.getInitializer(); // contains "expression"
            Debug.assertNonnull(init);
            // replace expressions by references to local variables
            for (int i = 0; i < exSize; i += 1) {
                replace(preceeding.get(i), tempVarRefs.get(i));
            }
            detach(init);
            // add initialization code to end of body
            CopyAssignment ca = f.createCopyAssignment(
                f.createVariableReference(f.createIdentifier(fs.getName())), init.deepClone());
            newParent = ca; // the new parent of the expression

            doAttach(ca, body, tempSize);
            // create class initializer block and add it to the type
            FieldDeclaration fd = (FieldDeclaration) fs.getParent();
            ClassInitializer ci = fd.isStatic() ? f.createClassInitializer(f.createStatic(), body)
                    : f.createClassInitializer(body);
            ci.makeAllParentRolesValid();
            TypeDeclaration tdecl = fd.getMemberParent();
            attach(ci, tdecl, tdecl.getMembers().indexOf(fd) + 1);
        }
    }

    /**
     * Returns the statement in a statement container or the field specification the given
     * expression is located within. Valid after analyze.
     */
    public NonTerminalProgramElement getTopMostParent() {
        return parent;
    }

    /**
     * After the transformation, returns the statement that contains the given expression. The
     * expression is now the first one that gets executed. <BR>
     * Take care that this transformation is actually called, even if the analysis resulted in an
     * identity.
     *
     * @return the statement containing the given expression.
     */
    public Statement getEnclosingStatement() {
        if (newParent == null) {
            throw new IllegalStateException("Only valid after transformation");
        }
        return newParent;
    }
}
