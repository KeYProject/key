/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Replaces references to var arg methods and var arg methods itself to make it java 1.4 compliant.
 * Does not change redefined/redefining from different compilation units, so that an entire
 * compilation unit list can be analyzed first before being executed. Note that this means that, if
 * used on a single compilation unit, this transformation may lead to incompilable code.
 *
 * @author Tobias Gutzmann
 * @since 0.80
 */
public class ResolveVarArgs extends TwoPassTransformation {
    private final CompilationUnit cu;
    private List<MethodDeclaration> varArgMeths;
    private List<MethodReference> refs;
    private List<List<Type>> sigs;
    private List<Type> lastParamTypes;

    public ResolveVarArgs(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    @Override
    public ProblemReport analyze() {
        varArgMeths = new ArrayList<>();
        refs = new ArrayList<>();
        sigs = new ArrayList<>();
        lastParamTypes = new ArrayList<>();
        TreeWalker tw = new TreeWalker(cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) pe;
                if (md.isVarArgMethod()) {
                    varArgMeths.add(md);
                    lastParamTypes.add(getSourceInfo().getType(
                        md.getParameterDeclarationAt(md.getParameterDeclarationCount() - 1)
                                .getTypeReference()));
                    List<MemberReference> rl = getCrossReferenceSourceInfo().getReferences(md);
                    for (MemberReference memberReference : rl) {
                        // if dimensions already match, don't add!!
                        MethodReference toAdd = (MethodReference) memberReference;
                        if (toAdd.getArguments() != null && toAdd.getArguments().size() == md
                                .getParameterDeclarationCount()) {
                            int idx = toAdd.getArguments().size() - 1;
                            Type tt = getSourceInfo().getType(toAdd.getExpressionAt(idx));
                            if (tt instanceof ArrayType && tt.equals(getSourceInfo().getType(
                                md.getParameterDeclarationAt(idx).getVariableSpecification()))) {
                                continue;
                            }
                        }
                        refs.add(toAdd);
                        sigs.add(getSourceInfo().getMethod(toAdd).getSignature());
                    }
                }
            }
        }
        return setProblemReport(NO_PROBLEM);
    }

    @Override
    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        // TODO may not trigger update !!
        int idx = 0;
        for (MethodReference mr : refs) {
            List<Type> sig = sigs.get(idx++);
            int from = sig.size() - 1;
            int cnt = mr.getArguments() == null ? 0 : mr.getArguments().size() - from;
            ASTList<Expression> eml = new ASTArrayList<>(cnt);
            for (int i = 0; i < cnt; i++) {
                eml.add(mr.getArguments().get(from + i).deepClone());
            }
            ArrayInitializer ai = f.createArrayInitializer(eml);
            NewArray na =
                f.createNewArray(TypeKit.createTypeReference(f, sig.get(sig.size() - 1)), 0, ai);
            MethodReference repl = mr.deepClone();
            while (cnt-- > 0) {
                repl.getArguments().remove(repl.getArguments().size() - 1);
            }
            if (repl.getArguments() == null) {
                repl.setArguments(new ASTArrayList<>(0));
            }
            repl.getArguments().add(na);
            repl.makeParentRoleValid();
            replace(mr, repl);
        }
        idx = 0;
        for (MethodDeclaration md : varArgMeths) {
            MethodDeclaration repl = md.deepClone();
            List<ParameterDeclaration> pds = md.getParameters();
            ParameterDeclaration pd = pds.get(pds.size() - 1);
            ParameterDeclaration newpd = f.createParameterDeclaration(
                TypeKit.createTypeReference(f,
                    getNameInfo().createArrayType(lastParamTypes.get(idx++))),
                pd.getVariableSpecification().getIdentifier().deepClone());
            newpd.setVarArg(false);
            replace(repl.getParameterDeclarationAt(repl.getParameterDeclarationCount() - 1), newpd);
            repl.makeParentRoleValid();
            replace(md, repl);
        }
    }
}
