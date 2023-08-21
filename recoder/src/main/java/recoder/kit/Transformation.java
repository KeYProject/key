/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ExpressionStatement;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.*;

/**
 * Default implementation of a transformation command object. This class takes a cross reference
 * service configuration suitable for transformations and provides access methods to frequently used
 * services.
 * <p>
 * Transformations should obey the following protocol:
 * <OL>
 * <LI>Initialization (constructor): Validate and store the transformation parameters.
 * <LI>Transformation (execute): Collect all semantic information via queries to the info services,
 * perform the necessary syntactic changes and report the effects of the transformation, setting the
 * problem report properly. A transformation should yield <CODE>IDENTITY</CODE> if it is not
 * necessary to perform it. This allows to avoid termination problems when falling back to a
 * back-tracking strategy for iterated transformations. <BR>
 * Visible transformations must report all changes they have done to the change history and must
 * mark their beginning before the first change. Changes are already reported by the convenience
 * tree manipulators attach(Role)/detach/replace.
 * <LI>Post mortem: Allow to access analysis results and generated syntax trees that might be useful
 * for other transformations, even after the transformation has been performed.
 * </OL>
 * <p>
 * Transformations may be used on syntax elements that are not yet visible to the model; in that
 * case, no change reports are generated. A partially visible transformation may change the state of
 * its visibility in between actions, but this should rarely be necessary.
 *
 * @author AL
 * @since 0.53
 */
public abstract class Transformation {

    public final static NoProblem NO_PROBLEM = new NoProblem();
    public final static Equivalence EQUIVALENCE = new Equivalence();
    public final static Identity IDENTITY = new Identity();
    private CrossReferenceServiceConfiguration serviceConfiguration;
    /**
     * The problem report as created by the analysis phase.
     */
    private ProblemReport report;

    /**
     * Creates a new transformation leaving open the given service configuration. This is useful for
     * bean-like transformation management.
     */
    protected Transformation() {
        // nothing to do
    }

    /**
     * Creates a new transformation using the given service configuration.
     *
     * @param sc the service configuration to use.
     */
    public Transformation(CrossReferenceServiceConfiguration sc) {
        setServiceConfiguration(sc);
    }

    /**
     * Replaces a single child by a different one without reporting. This method performs the
     * exchange but does not handle the change history notification. The method does not do anything
     * with compilation units and assumes that the parent link is defined for all other types.
     *
     * @param child the child to remove from its parent.
     * @param replacement the child to replace its original (must be of appropriate type).
     */
    public static void doReplace(ProgramElement child, ProgramElement replacement) {
        if (child == replacement) {
            return;
        }
        NonTerminalProgramElement parent = child.getASTParent();
        // compilation units may have a null parent
        if (parent != null) {
            parent.replaceChild(child, replacement);
        }
    }

    /**
     * Detaches a subtree without reporting. This method performs the deletion of the child link but
     * does not handle the change history notification. The method does not do anything with childs
     * that have no parent links such as compilation units.
     *
     * @param root the root of the subtree to remove.
     */
    public static void doDetach(ProgramElement root) {
        NonTerminalProgramElement parent = root.getASTParent();
        if (parent != null) {
            parent.replaceChild(root, null);
        }
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Identifier child, NamedProgramElement parent) {
        parent.setIdentifier(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Import child, CompilationUnit parent, int index) {
        ASTList<Import> list = parent.getImports();
        if (list == null) {
            parent.setImports(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(PackageSpecification child, CompilationUnit parent) {
        parent.setPackageSpecification(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Statement child, StatementBlock parent, int index) {
        ASTList<Statement> list = parent.getBody();
        if (list == null) {
            parent.setBody(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, MethodDeclaration parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, ClassInitializer parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Statement child, Case parent, int index) {
        ASTList<Statement> list = parent.getBody();
        if (list == null) {
            parent.setBody(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Statement child, Default parent, int index) {
        ASTList<Statement> list = parent.getBody();
        if (list == null) {
            parent.setBody(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, Catch parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, Finally parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, Try parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Statement child, Then parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Statement child, Else parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, LoopStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Statement child, LabeledStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(StatementBlock child, SynchronizedBlock parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    // recoder.java.*

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(TypeDeclaration child, CompilationUnit parent, int index) {
        ASTList<TypeDeclaration> list = parent.getDeclarations();
        if (list == null) {
            parent.setDeclarations(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(ClassDeclaration child, StatementBlock parent, int index) {
        ASTList<Statement> list = parent.getBody();
        if (list == null) {
            parent.setBody(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ClassDeclaration child, New parent) {
        parent.setClassDeclaration(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(MemberDeclaration child, TypeDeclaration parent, int index) {
        ASTList<MemberDeclaration> list = parent.getMembers();
        if (list == null) {
            parent.setMembers(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setMemberParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(ParameterDeclaration child, MethodDeclaration parent, int index) {

        ASTList<ParameterDeclaration> list = parent.getParameters();
        if (list == null) {
            parent.setParameters(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParameterContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ParameterDeclaration child, Catch parent) {
        parent.setParameterDeclaration(child);
        child.setParameterContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(DeclarationSpecifier child, Declaration parent, int index) {
        ASTList<DeclarationSpecifier> list = parent.getDeclarationSpecifiers();
        if (list == null) {
            parent.setDeclarationSpecifiers(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    // the other variant of attachment to a case has no index field;
    // hence overloading is no problem for expression statements

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Throws child, MethodDeclaration parent) {
        parent.setThrown(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Implements child, ClassDeclaration parent) {
        parent.setImplementedTypes(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Extends child, ClassDeclaration parent) {
        parent.setExtendedTypes(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Extends child, InterfaceDeclaration parent) {
        parent.setExtendedTypes(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(FieldSpecification child, FieldDeclaration parent, int index) {

        ASTList<FieldSpecification> list = parent.getFieldSpecifications();
        if (list == null) {
            parent.setFieldSpecifications(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(VariableSpecification child, LocalVariableDeclaration parent,
            int index) {

        ASTList<VariableSpecification> list = parent.getVariableSpecifications();
        if (list == null) {
            parent.setVariableSpecifications(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(VariableSpecification child, ParameterDeclaration parent) {
        parent.setVariableSpecification(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsBody(Statement child, LoopStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsInitializer(LoopInitializer child, For parent) {
        ASTList<LoopInitializer> list = parent.getInitializers();
        if (list == null) {
            parent.setInitializers(list = new ASTArrayList<>());
        }
        list.add(0, child);
        child.setStatementContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsCondition(Expression child, Assert parent) {
        parent.setCondition(child);
        child.setExpressionContainer(parent);
    }

    // recoder.java.declaration.*

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsMessage(Expression child, Assert parent) {
        parent.setMessage(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsGuard(Expression child, LoopStatement parent) {
        parent.setGuard(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsUpdate(ExpressionStatement child, For parent, int index) {
        ASTList<Expression> list = parent.getUpdates();
        if (list == null) {
            parent.setUpdates(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Then child, If parent) {
        parent.setThen(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Else child, If parent) {
        parent.setElse(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Catch child, Try parent, int index) {
        ASTList<Branch> list = parent.getBranchList();
        if (list == null) {
            parent.setBranchList(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Finally child, Try parent, int index) {
        ASTList<Branch> list = parent.getBranchList();
        if (list == null) {
            parent.setBranchList(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Case child, Switch parent, int index) {
        ASTList<Branch> list = parent.getBranchList();
        if (list == null) {
            parent.setBranchList(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(Default child, Switch parent, int index) {
        ASTList<Branch> list = parent.getBranchList();
        if (list == null) {
            parent.setBranchList(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ReferencePrefix child, ArrayLengthReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsPrefix(ReferencePrefix child, ArrayReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, ArrayReference parent, int index) {
        ASTList<Expression> list = parent.getDimensionExpressions();
        if (list == null) {
            parent.setDimensionExpressions(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ReferencePrefix child, FieldReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsPrefix(TypeReference child, MetaClassReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsPrefix(ReferencePrefix child, MethodReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, MethodReference parent, int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    // recoder.java.statement.*

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(PackageReference child, PackageReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ReferencePrefix child, SuperReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(TypeReference child, ThisReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ReferencePrefix child, TypeReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ReferencePrefix child, UncollatedReferenceQualifier parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(ArrayInitializer child, NewArray parent) {
        parent.setArrayInitializer(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttach(ArrayInitializer child, ArrayInitializer parent, int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Expression child, VariableSpecification parent) {
        parent.setInitializer(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Expression child, ExpressionJumpStatement parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Expression child, If parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    // recoder.java.reference.*

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttach(Expression child, Switch parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsLabel(Expression child, Case parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsPrefix(ReferencePrefix child, New parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, Operator parent, int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, SpecialConstructorReference parent,
            int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsArgument(TypeReference child, TypeOperator parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsArgument(Expression child, TypeCast parent) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(0, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    public static void doAttachAsArgument(Expression child, Instanceof parent) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(0, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, New parent, int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    public static void doAttachAsArgument(Expression child, NewArray parent, int index) {
        ASTList<Expression> list = parent.getArguments();
        if (list == null) {
            parent.setArguments(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setExpressionContainer(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @since 0.72
     */
    public static void doAttach(TypeReference child, Import parent) {
        parent.setReference(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @since 0.72
     */
    public static void doAttach(PackageReference child, Import parent) {
        parent.setReference(child);
        child.setParent(parent);
    }

    // recoder.java.expression.*

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @since 0.72
     */
    public static void doAttach(PackageReference child, PackageSpecification parent) {
        parent.setPackageReference(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     * @since 0.72
     */
    public static void doAttach(TypeReference child, InheritanceSpecification parent, int index) {
        ASTList<TypeReference> list = parent.getSupertypes();
        if (list == null) {
            parent.setSupertypes(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @since 0.72
     */
    public static void doAttach(TypeReference child, MethodDeclaration parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @since 0.72
     */
    public static void doAttach(TypeReference child, VariableDeclaration parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    /**
     * Attaches a child node to a parent node at a given index but does not report this.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     * @since 0.72
     */
    public static void doAttach(TypeReference child, Throws parent, int index) {
        ASTList<TypeReference> list = parent.getExceptions();
        if (list == null) {
            parent.setExceptions(list = new ASTArrayList<>());
        }
        list.add(index, child);
        child.setParent(parent);
    }

    public CrossReferenceServiceConfiguration getServiceConfiguration() {
        return serviceConfiguration;
    }

    /**
     * Sets the service configuration to use for this transformation.
     *
     * @param sc the service configuration to use, may not be <CODE>null
     *           </CODE>. UA: thou shalt not forbid public access if others want to inherit!!!
     */
    public void setServiceConfiguration(CrossReferenceServiceConfiguration sc) {
        if (sc == null) {
            throw new IllegalArgumentException(
                "A transformation needs a service configuration to work");
        }
        serviceConfiguration = sc;
    }

    /**
     * Checks if this transformation is meant to be visible and shall report changes to the model.
     * If a transformation is not visible, it may not change parts of the current model. This
     * default implementation returns <CODE>true</CODE>.
     *
     * @return <CODE>true</CODE>.
     */
    public boolean isVisible() {
        return true;
    }

    /**
     * Returns the program factory service contained in the service configuration.
     *
     * @return the current program factory.
     * @see #getServiceConfiguration()
     */
    protected ProgramFactory getProgramFactory() {
        return serviceConfiguration.getProgramFactory();
    }

    /**
     * Returns the change history service contained in the service configuration.
     *
     * @return the current change history.
     * @see #getServiceConfiguration()
     */
    protected ChangeHistory getChangeHistory() {
        return serviceConfiguration.getChangeHistory();
    }

    /**
     * Returns the source info service contained in the service configuration. This method will
     * return the same object as {@link #getCrossReferenceSourceInfo()}.
     *
     * @return the current source info.
     * @see #getServiceConfiguration()
     */
    protected SourceInfo getSourceInfo() {
        return serviceConfiguration.getSourceInfo();
    }

    /**
     * Returns the cross reference source info service contained in the service configuration.
     *
     * @return the current cross reference source info.
     * @see #getServiceConfiguration()
     */
    protected CrossReferenceSourceInfo getCrossReferenceSourceInfo() {
        return serviceConfiguration.getCrossReferenceSourceInfo();
    }

    /**
     * Returns the name info service contained in the service configuration.
     *
     * @return the current name info.
     * @see #getServiceConfiguration()
     */
    protected NameInfo getNameInfo() {
        return serviceConfiguration.getNameInfo();
    }

    /**
     * Returns the source file repository service contained in the service configuration.
     *
     * @return the current source file repository.
     * @see #getServiceConfiguration()
     */
    protected SourceFileRepository getSourceFileRepository() {
        return serviceConfiguration.getSourceFileRepository();
    }

    // recoder.java.*

    /**
     * Performs the transformation. Prepares all necessary information, checks the transformation
     * requirements, and performs the syntactic changes if the report was NoProblem and not
     * Identity. This method should also set the problem report to be fetched later on. The default
     * implementation does nothing and reports Identity.
     *
     * @return a problem report.
     */
    public ProblemReport execute() {
        return setProblemReport(IDENTITY);
    }

    /**
     * Returns the problem report.
     *
     * @return the problem report of this transformation, or <CODE>null</CODE> if the transformation
     *         has not yet been applied.
     */
    public ProblemReport getProblemReport() {
        return report;
    }

    /**
     * Sets the problem report. This should be done by {@link #execute}.
     *
     * @param report the problem report.
     * @return the problem report (passed through).
     */
    protected ProblemReport setProblemReport(ProblemReport report) {
        return this.report = report;
    }

    /**
     * Reverts all changes of this transformation including all changes of transformations that have
     * been triggered during the transformation phase from there on. This method will do nothing for
     * invisible transformations, as only visible transformations report their changes to the change
     * history.
     * <p>
     * If this object is a {@link recoder.kit.TwoPassTransformation}, a redo should be possible via
     * a second call to {@link recoder.kit.TwoPassTransformation#transform()}.
     *
     * @throws NoSuchTransformationException if the given transformation is not known, for instance
     *         if it has already been removed.
     * @see recoder.service.ChangeHistory#rollback(Transformation)
     */
    public void rollback() throws NoSuchTransformationException {
        if (isVisible()) {
            getChangeHistory().rollback(this);
        }
    }

    /**
     * Returns a short description of this transformation. The default implementation will return
     * the last part of the class name.
     *
     * @return a short description of this transformation.
     */
    public String toString() {
        String result = getClass().getName();
        int ldp = result.lastIndexOf('.');
        if (ldp > 0) {
            result = result.substring(ldp + 1);
        }
        return result;
    }

    /**
     * Replaces a single child by a different one. This method performs the exchange and handles the
     * change history notification. The method can also handle compilation units properly, but
     * otherwise assumes that the parent link is defined.
     *
     * @param child the child to remove from its parent.
     * @param replacement the child to replace its original (must be of appropriate type).
     */
    protected final void replace(ProgramElement child, ProgramElement replacement) {
        if (child == replacement) {
            return;
        }
        NonTerminalProgramElement parent = child.getASTParent();
        // compilation units may have a null parent
        if (parent != null) {
            parent.replaceChild(child, replacement);
        }
        if (isVisible()) {
            getChangeHistory().replaced(child, replacement);
        }
    }

    // the other variant of attachment to a case has no index field;
    // hence overloading is no problem for expression statements

    /**
     * Detaches a subtree. This method performs the deletion of the child link and handles the
     * change history notification. The method can also handle compilation units properly, but
     * otherwise assumes that the parent link is defined.
     *
     * @param root the root of the subtree to remove.
     */
    protected final void detach(ProgramElement root) {
        NonTerminalProgramElement parent = root.getASTParent();
        int position;
        if (parent != null) {
            position = parent.getChildPositionCode(root);
            parent.replaceChild(root, null);
        } else {
            position = 0;
        }
        if (isVisible()) {
            getChangeHistory().detached(root, position);
        }
    }

    /**
     * Registers a compilation unit.
     *
     * @param child the unit to register.
     */
    protected final void attach(CompilationUnit child) {
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Identifier child, NamedProgramElement parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Import child, CompilationUnit parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(PackageSpecification child, CompilationUnit parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Statement child, StatementBlock parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, MethodDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, ClassInitializer parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Statement child, Case parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Statement child, Default parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    // recoder.java.declaration.*

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, Catch parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, Finally parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, Try parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Statement child, Then parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Statement child, Else parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, LoopStatement parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Statement child, LabeledStatement parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(StatementBlock child, SynchronizedBlock parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(TypeDeclaration child, CompilationUnit parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(ClassDeclaration child, StatementBlock parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ClassDeclaration child, New parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(MemberDeclaration child, TypeDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(ParameterDeclaration child, MethodDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ParameterDeclaration child, Catch parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Modifier child, Declaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Throws child, MethodDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    // recoder.java.statement.*

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Implements child, ClassDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Extends child, ClassDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Extends child, InterfaceDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(FieldSpecification child, FieldDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(VariableSpecification child, LocalVariableDeclaration parent,
            int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(VariableSpecification child, ParameterDeclaration parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsBody(Statement child, LoopStatement parent) {
        doAttachAsBody(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsInitializer(LoopInitializer child, For parent) {
        doAttachAsInitializer(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsGuard(Expression child, LoopStatement parent) {
        doAttachAsGuard(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsUpdate(ExpressionStatement child, For parent, int index) {
        doAttachAsUpdate(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    // recoder.java.reference.*

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsCondition(Expression child, Assert parent) {
        doAttachAsCondition(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsMessage(Expression child, Assert parent) {
        doAttachAsMessage(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Then child, If parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Else child, If parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Catch child, Try parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Finally child, Try parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Case child, Switch parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(Default child, Switch parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ReferencePrefix child, ArrayLengthReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsPrefix(ReferencePrefix child, ArrayReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, ArrayReference parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ReferencePrefix child, FieldReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    // recoder.java.expression.*

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsPrefix(TypeReference child, MetaClassReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsPrefix(ReferencePrefix child, MethodReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, MethodReference parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(PackageReference child, PackageReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ReferencePrefix child, SuperReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(TypeReference child, ThisReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ReferencePrefix child, TypeReference parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ReferencePrefix child, UncollatedReferenceQualifier parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(ArrayInitializer child, NewArray parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attach(ArrayInitializer child, ArrayInitializer parent, int index) {
        doAttach(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Expression child, VariableSpecification parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Expression child, ExpressionJumpStatement parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Expression child, If parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attach(Expression child, Switch parent) {
        doAttach(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsLabel(Expression child, Case parent) {
        doAttachAsLabel(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsPrefix(ReferencePrefix child, New parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, Operator parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, SpecialConstructorReference parent,
            int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsArgument(TypeReference child, TypeOperator parent) {
        doAttachAsArgument(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     */
    protected final void attachAsArgument(Expression child, TypeCast parent) {
        doAttachAsArgument(child, parent);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, New parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

    /**
     * Attaches a child node to a parent node at a given index and reports this if necessary.
     *
     * @param child the child node to attach.
     * @param parent the parent node to attach the child to.
     * @param index the requested child position.
     */
    protected final void attachAsArgument(Expression child, NewArray parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible()) {
            getChangeHistory().attached(child);
        }
    }

}
