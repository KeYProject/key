/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.operator.LogicalOr;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.FieldReference;
import recoder.java.statement.*;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;

/**
 * untested for enum declarations nested within enum declarations
 *
 * @author Tobias Gutzmann
 */
public class ReplaceEnums extends TwoPassTransformation {


    private final CompilationUnit cu;
    private List<ReplaceSingleEnum> parts;

    /**
     *
     */
    public ReplaceEnums(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    @Override
    public ProblemReport analyze() {
        parts = new ArrayList<>();
        TreeWalker tw = new TreeWalker(cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof EnumDeclaration) {
                ReplaceSingleEnum p =
                    new ReplaceSingleEnum(getServiceConfiguration(), (EnumDeclaration) pe);
                p.analyze();
                parts.add(p);
            }
        }

        return super.analyze();
    }

    @Override
    public void transform() {
        super.transform();
        for (int i = parts.size() - 1; i >= 0; i--) {
            parts.get(i).transform();
        }
    }

    public static class ReplaceSingleEnum extends TwoPassTransformation {
        private final EnumDeclaration ed;
        private ClassDeclaration repl;
        private Set<Switch> switchStmnts;
        private Map<Switch, String[]> names;

        public ReplaceSingleEnum(CrossReferenceServiceConfiguration sc, EnumDeclaration ed) {
            super(sc);
            this.ed = ed;
        }

        @Override
        public ProblemReport analyze() {
            switchStmnts = new HashSet<>();
            names = new HashMap<>();
            ProgramFactory f = getProgramFactory();
            repl = f.createClassDeclaration();
            if (ed.getDeclarationSpecifiers() != null) {
                repl.setDeclarationSpecifiers(ed.getDeclarationSpecifiers().deepClone());
            } else {
                repl.setDeclarationSpecifiers(new ASTArrayList<>(1));
            }
            if (ed.isFinal()) {
                repl.getDeclarationSpecifiers().add(f.createFinal());
            }
            if (ed.getComments() != null) {
                repl.setComments(ed.getComments().deepClone());
            }
            ASTArrayList<MemberDeclaration> mlist =
                new ASTArrayList<>(ed.getMembers().size());
            repl.setMembers(mlist);
            repl.setIdentifier(ed.getIdentifier().deepClone());
            // needed later for valueOf() and values()
            ASTArrayList<FieldSpecification> enumSpecRepl = new ASTArrayList<>();
            for (int i = 0; i < ed.getMembers().size(); i++) {
                MemberDeclaration md = ed.getMembers().get(i);
                if (md instanceof EnumConstantDeclaration) {
                    EnumConstantDeclaration ec = (EnumConstantDeclaration) md;
                    EnumConstantSpecification ecs = ec.getEnumConstantSpecification();

                    // create replacement for current constant
                    ASTArrayList<DeclarationSpecifier> dsml =
                        new ASTArrayList<>();
                    if (ec.getAnnotations() == null) {
                        for (AnnotationUseSpecification a : ec.getAnnotations()) {
                            dsml.add(a.deepClone());
                        }
                    }
                    dsml.add(f.createFinal());
                    dsml.add(f.createPublic());
                    dsml.add(f.createStatic());
                    FieldDeclaration fd = f.createFieldDeclaration(dsml,
                        f.createTypeReference(ed.getIdentifier().deepClone()),
                        ecs.getIdentifier().deepClone(), null);
                    FieldSpecification fs = fd.getFieldSpecifications().get(0);

                    // update references: parent instanceof Switch ?
                    List<FieldReference> frl = getCrossReferenceSourceInfo().getReferences(ecs);
                    for (FieldReference fr : frl) {
                        if (fr.getASTParent() instanceof Case) {
                            Switch sw = (Switch) fr.getASTParent().getASTParent();
                            switchStmnts.add(sw);
                            String fallThroughName = VariableKit
                                    .createValidVariableName(getSourceInfo(), sw, "fallThrough");
                            String doneAnyName =
                                VariableKit.createValidVariableName(getSourceInfo(), sw, "doneAny");
                            names.put(sw, new String[] { fallThroughName, doneAnyName });
                        }
                    }

                    New e = f.createNew();
                    e.setTypeReference(f.createTypeReference(repl.getIdentifier()));
                    if (ecs.getConstructorReference().getArguments() != null
                            || ecs.getConstructorReference().getClassDeclaration() != null) {
                        List<Expression> ecsargs = ecs.getConstructorReference().getArguments();
                        int s = ecsargs == null ? 0 : ecsargs.size();
                        ASTArrayList<Expression> args = new ASTArrayList<>(s);
                        e.setArguments(args);
                        for (int j = 0; j < s; j++) {
                            args.add(ecsargs.get(j).deepClone());
                        }
                        if (ecs.getConstructorReference().getClassDeclaration() != null) {
                            e.setClassDeclaration(
                                ecs.getConstructorReference().getClassDeclaration().deepClone());
                        }
                    }
                    fs.setInitializer(e);
                    e.makeParentRoleValid();
                    fs.makeParentRoleValid();
                    fd.makeParentRoleValid();
                    enumSpecRepl.add(fs);
                    mlist.add(fd);
                } else {
                    mlist.add((MemberDeclaration) md.deepClone());
                }
            }
            // now add values(), valueOf(), and ordinal
            MethodDeclaration values = f.createMethodDeclaration();
            MethodDeclaration valueOf = f.createMethodDeclaration();
            MethodDeclaration ordinal = f.createMethodDeclaration();
            values.setIdentifier(f.createIdentifier("values"));
            valueOf.setIdentifier(f.createIdentifier("valueOf"));
            ordinal.setIdentifier(f.createIdentifier("ordinal"));
            ASTArrayList<DeclarationSpecifier> declSpecs = new ASTArrayList<>();
            declSpecs.add(f.createPublic());
            declSpecs.add(f.createStatic());
            values.setDeclarationSpecifiers(declSpecs);
            // clone for valueOf()
            declSpecs = declSpecs.deepClone();
            valueOf.setDeclarationSpecifiers(declSpecs);
            // clone/change for ordinal()
            declSpecs = declSpecs.deepClone();
            declSpecs.remove(1);
            declSpecs.add(f.createFinal());
            ordinal.setDeclarationSpecifiers(declSpecs);
            values.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone(), 1));
            valueOf.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone()));
            ordinal.setTypeReference(f.createTypeReference(f.createIdentifier("int")));
            valueOf.setParameters(
                new ASTArrayList<>(f.createParameterDeclaration(
                    TypeKit.createTypeReference(f, "String"), f.createIdentifier("name"))));
            // now, add functional behaviour
            StatementBlock valuesSt = f.createStatementBlock();
            StatementBlock valueOfSt = f.createStatementBlock();
            StatementBlock ordinalSt = f.createStatementBlock();
            values.setBody(valuesSt);
            valueOf.setBody(valueOfSt);
            ordinal.setBody(ordinalSt);

            // ordinal first
            ordinalSt.setBody(new ASTArrayList<>(
                f.createReturn(f.createFieldReference(f.createIdentifier("ordinal")))));

            // na must be filled for values, ite iteratively extended
            NewArray na = f.createNewArray();
            na.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone(), 1));
            na.setArrayInitializer(
                f.createArrayInitializer(new ASTArrayList<>(enumSpecRepl.size())));
            na.makeParentRoleValid();
            valuesSt.setBody(new ASTArrayList<>(f.createReturn(na)));
            If ite = f.createIf();
            // TODO doesn't work if no enum constants are declared (makes no sense, but yet...)
            valueOfSt.setBody(new ASTArrayList<>(ite));
            for (int i = 0; i < enumSpecRepl.size(); i++) {
                FieldSpecification fs = enumSpecRepl.get(i);
                na.getArrayInitializer().getArguments()
                        .add(f.createFieldReference(fs.getIdentifier().deepClone()));
                ite.setExpression(f.createMethodReference(
                    f.createVariableReference(f.createIdentifier("name")),
                    f.createIdentifier("equals"),
                    new ASTArrayList<>(f.createStringLiteral("\"" + fs.getName() + "\""))

                ));
                ite.setThen(f.createThen(
                    f.createReturn(f.createFieldReference(fs.getIdentifier().deepClone()))));
                if (i + 1 < enumSpecRepl.size()) {
                    ite.setElse(f.createElse(f.createIf()));
                    ite.makeParentRoleValid();
                    ite = (If) ite.getElse().getStatementAt(0);
                } else {
                    ite.makeParentRoleValid();
                }
            }
            na.getArrayInitializer().makeParentRoleValid();
            ite.setElse(f.createElse(f.createThrow(f.createNew(null,
                f.createTypeReference(f.createIdentifier("IllegalArgumentException")), null))));
            ite.makeParentRoleValid();
            valuesSt.makeParentRoleValid();
            valueOfSt.makeParentRoleValid();
            ordinalSt.makeParentRoleValid();

            valueOf.makeParentRoleValid();
            values.makeParentRoleValid();
            ordinal.makeParentRoleValid();
            mlist.add(valueOf);
            mlist.add(values);
            mlist.add(ordinal);
            // also add fields for ordinal
            declSpecs = new ASTArrayList<>(2);
            declSpecs.add(f.createPrivate());
            declSpecs.add(f.createStatic());
            mlist.add(f.createFieldDeclaration(declSpecs,
                f.createTypeReference(f.createIdentifier("int")),
                f.createIdentifier("CURRENT_ORDINAL"), f.createIntLiteral("0")));
            declSpecs = new ASTArrayList<>(2);
            declSpecs.add(f.createPrivate());
            declSpecs.add(f.createFinal());
            mlist.add(f.createFieldDeclaration(declSpecs,
                f.createTypeReference(f.createIdentifier("int")), f.createIdentifier("ordinal"),
                f.createPostIncrement(
                    f.createFieldReference(f.createIdentifier("CURRENT_ORDINAL")))));
            // done
            repl.makeParentRoleValid();
            MiscKit.unindent(repl);
            return super.analyze();
        }

        @Override
        public void transform() {
            super.transform();
            replace(ed, repl);
            for (Switch sw : switchStmnts) {
                ProgramFactory f = getProgramFactory();
                ASTArrayList<Statement> sml = new ASTArrayList<>();
                StatementBlock sb = f.createStatementBlock(sml);
                String[] nm = names.get(sw);
                String fallThroughName = nm[0];
                String doneAnyName = nm[1];
                // helper variables
                sml.add(f.createLocalVariableDeclaration(null,
                    f.createTypeReference(f.createIdentifier("boolean")),
                    f.createIdentifier(fallThroughName), f.createBooleanLiteral(false)));
                sml.add(f.createLocalVariableDeclaration(null,
                    f.createTypeReference(f.createIdentifier("boolean")),
                    f.createIdentifier(doneAnyName), f.createBooleanLiteral(false)));
                Do repl = f.createDo(f.createBooleanLiteral(false), sb);
                for (int i = 0; i < sw.getBranchCount(); i++) {
                    Branch b = sw.getBranchAt(i);
                    if (b instanceof Default) {
                        if (i != sw.getBranchCount() - 1) {
                            throw new ModelException("case after default is illegal");
                        }
                        Default d = (Default) b;
                        ASTArrayList<Statement> defaultStmnt = new ASTArrayList<>();
                        StatementBlock sb2 = f.createStatementBlock(defaultStmnt);
                        LogicalOr cond = f.createLogicalOr(
                            f.createVariableReference(f.createIdentifier(doneAnyName)),
                            f.createVariableReference(f.createIdentifier(fallThroughName)));
                        defaultStmnt.addAll(d.getBody().deepClone());
                        sb2.makeParentRoleValid();
                        Then then = f.createThen(sb2);
                        If newIf = f.createIf(cond, then);
                        sml.add(newIf);
                    } else {
                        Case c = (Case) b;
                        LogicalOr cond = f.createLogicalOr(
                            f.createVariableReference(f.createIdentifier(fallThroughName)),
                            f.createEquals(
                                // VariableKit.createVariableReference((FieldDeclaration)((FieldSpecification)getSourceInfo().getField((FieldReference)c.getExpression())).getASTParent()),
                                f.createFieldReference(
                                    TypeKit.createTypeReference(f, ed.getFullName()),
                                    f.createIdentifier(
                                        ((FieldReference) c.getExpression()).getName())),
                                sw.getExpression().deepClone()));
                        ASTArrayList<Statement> thenStmnt = new ASTArrayList<>();
                        StatementBlock sb2 = f.createStatementBlock(thenStmnt);
                        // do not go in default if we entered any other branch:
                        thenStmnt.add(f.createCopyAssignment(
                            f.createVariableReference(f.createIdentifier(doneAnyName)),
                            f.createBooleanLiteral(true)));
                        // reset fall through
                        thenStmnt.add(f.createCopyAssignment(
                            f.createVariableReference(f.createIdentifier(fallThroughName)),
                            f.createBooleanLiteral(false)));
                        // copy original statements:
                        thenStmnt.addAll(c.getBody().deepClone());
                        // if we reach this, fall through:
                        if (c.getBody().size() == 0 || !(c.getBody()
                                .get(c.getBody().size() - 1) instanceof JumpStatement)) {
                            thenStmnt.add(f.createCopyAssignment(
                                f.createVariableReference(f.createIdentifier(fallThroughName)),
                                f.createBooleanLiteral(true)));
                        }
                        sb2.makeParentRoleValid();
                        Then then = f.createThen(sb2);
                        If newIf = f.createIf(cond, then);
                        sml.add(newIf);
                    }
                }
                sb.makeParentRoleValid();
                MiscKit.unindent(repl);
                replace(sw, repl);
            }
        }
    }

}
