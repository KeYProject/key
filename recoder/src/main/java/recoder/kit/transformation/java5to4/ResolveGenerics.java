/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.bytecode.MethodInfo;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.Assignment;
import recoder.java.expression.operator.New;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Return;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.service.CrossReferenceSourceInfo;

/**
 * This transformation does not work yet!
 *
 * @author Tobias Gutzmann
 */
public class ResolveGenerics extends TwoPassTransformation {

    private final CompilationUnit cu;
    private List<TwoPassTransformation> parts;
    private List<ProgramElement> stuffToBeRemoved;
    private List<TwoPassTransformation> trParts;

    /**
     * @param sc
     */
    public ResolveGenerics(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;

    }

    private static void analyze(ProgramFactory f, CrossReferenceSourceInfo ci,
            List<TypeParameterDeclaration> typeParams, List<ProgramElement> stuffToBeRemoved,
            List<IntroduceCast> casts, List<TypeParamRefReplacement> typeParamReferences) {
        // deal with type parameter uses in own Type Declaration first
        for (TypeParameterDeclaration tpd : typeParams) {
            TypeReference repl;
            ClassType resolvedType;
            if (tpd.getBounds() == null || tpd.getBounds().size() == 0) {
                resolvedType = ci.getServiceConfiguration().getNameInfo().getJavaLangObject();
                repl = TypeKit.createTypeReference(ci, resolvedType, tpd); // in rare cases where
                // another type named
                // "Object" is used (e.g.
                // Corba applications)
            } else {
                resolvedType = (ClassType) ci.getType(tpd.getBounds().get(0));
                repl = makeReplacement(f, tpd);
            }
            Type rt = tpd;
            // TODO wtf is this intended to do ????
            // int dim = 0;
            do {
                List<TypeReference> tprl = ci.getReferences(rt);
                for (TypeReference tr : tprl) {
                    if (!(tr.getASTParent() instanceof TypeArgumentDeclaration)) {
                        typeParamReferences.add(new TypeParamRefReplacement(tr, repl.deepClone()));
                    } else {
                        stuffToBeRemoved.add(tr.getASTParent());
                    }

                    boolean alwaysCast = false;
                    while (tr.getASTParent() instanceof TypeArgumentDeclaration) {
                        tr = (TypeReference) tr.getASTParent().getASTParent();
                        alwaysCast = true;
                    }

                    if (tr.getASTParent() instanceof MethodDeclaration) {
                        // may need to introduce some extra type casts for additional bounds...
                        MethodDeclaration md = (MethodDeclaration) tr.getASTParent();
                        List<MemberReference> mrl = ci.getReferences(md);
                        for (MemberReference memberReference : mrl) {
                            MethodReference mr = (MethodReference) memberReference;
                            NonTerminalProgramElement parent = mr.getASTParent();
                            if (parent instanceof MethodReference) {
                                // find out what type's method is referenced
                                ClassType tmpResolved = resolvedType;
                                MethodReference pr = (MethodReference) parent;
                                do {
                                    // need to deal with reference suffixes, too!
                                    ClassType target = ci.getMethod(pr).getContainingClassType();
                                    if (target != null && !(target instanceof TypeParameter)
                                            && (!ci.isSubtype(tmpResolved, target) || alwaysCast)) {
                                        casts.add(new IntroduceCast(mr,
                                            TypeKit.createTypeReference(ci, target, parent)));
                                    }
                                    if (pr.getReferenceSuffix() instanceof MethodReference) {
                                        Type tmp = ci.getType(pr);
                                        if (!(tmp instanceof ClassType)) {
                                            break;
                                        }
                                        tmpResolved = (ClassType) tmp;
                                        mr = pr;
                                        pr = (MethodReference) pr.getReferenceSuffix();
                                    } else {
                                        break;
                                    }
                                } while (true);
                            } else if (parent instanceof Expression
                                    || parent instanceof VariableSpecification
                                    || parent instanceof Return) {
                                Type target;
                                if (parent instanceof Return) {
                                    while (!(parent instanceof MethodDeclaration)) {
                                        parent = parent.getASTParent();
                                    }
                                    target = ((MethodDeclaration) parent).getReturnType();
                                } else {
                                    target = ci.getType(parent);
                                }
                                if (!(target instanceof PrimitiveType)
                                        && !ci.isSubtype(resolvedType, (ClassType) target)
                                        && !(target instanceof TypeParameter)) {
                                    // type cast needed
                                    casts.add(new IntroduceCast(mr,
                                        TypeKit.createTypeReference(ci, target, mr)));
                                }
                                // may also need to cast rhs of assignment
                                if (parent instanceof Assignment) {
                                    Assignment as = (Assignment) parent;
                                    if (as.getExpressionAt(0) == mr) {
                                        casts.add(new IntroduceCast(as, TypeKit.createTypeReference(
                                            ci, target, as.getExpressionAt(1))));
                                    }
                                }
                            }
                        }
                    }
                }
                rt = ci.getServiceConfiguration().getNameInfo().getArrayType(rt);
                // dim++;
                repl.setDimensions(repl.getDimensions() + 1);
            } while (rt != null);
        }
    }

    private static TypeReference makeReplacement(ProgramFactory f, TypeParameterDeclaration tpd) {
        TypeReference repl;
        repl = tpd.getBounds().get(0).deepClone();
        if (tpd.getBoundCount() > 1) {
            StringBuilder text = new StringBuilder("/*");
            for (int x = 1; x < tpd.getBoundCount(); x++) {
                text.append(" & ");
                text.append(tpd.getBoundName(x));
            }
            text.append(" */");
            repl.setComments(new ASTArrayList<>(f.createComment(text.toString(), false)));
        }
        return repl;
    }

    @Override
    public ProblemReport analyze() {
        parts = new ArrayList<>();
        stuffToBeRemoved = new ArrayList<>();
        trParts = new ArrayList<>();
        TreeWalker tw = new TreeWalker(cu);

        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            NonTerminalProgramElement parent = pe.getASTParent();
            if (pe instanceof TypeDeclaration && !(pe instanceof TypeParameterDeclaration)) {
                ResolveSingleGenericType p =
                    new ResolveSingleGenericType(getServiceConfiguration(), (TypeDeclaration) pe);
                if (p.analyze() != IDENTITY) {
                    parts.add(p);
                }
            } else if (pe instanceof MethodDeclaration) {
                ResolveGenericMethod p =
                    new ResolveGenericMethod(getServiceConfiguration(), (MethodDeclaration) pe);
                if (p.analyze() != IDENTITY) {
                    parts.add(p);
                }
            } else if (pe instanceof TypeReference) {
                TwoPassTransformation p;
                TypeReference tr = (TypeReference) pe;
                if (parent instanceof MethodDeclaration) {
                    MethodDeclaration md = (MethodDeclaration) parent;
                    if (md.getTypeReference() != tr) {
                        continue; // argument, not return type
                    }
                    Type t = getSourceInfo().getType(tr);
                    if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
                        CompilationUnit tcu = UnitKit.getCompilationUnit((TypeDeclaration) t);
                        if (tcu == cu) {
                            continue;
                        }
                    }
                    p = new ResolveMethodReturnType(getServiceConfiguration(), md);
                } else if (parent instanceof VariableDeclaration) {
                    Type t = getSourceInfo().getType(tr);
                    if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
                        CompilationUnit tcu = UnitKit.getCompilationUnit((TypeDeclaration) t);
                        if (tcu == cu) {
                            continue;
                        }
                    }
                    VariableDeclaration vd = (VariableDeclaration) parent;
                    p = new ResolveSingleVariableDeclaration(getServiceConfiguration(), vd);
                } else if (parent instanceof InheritanceSpecification) {
                    // InheritanceSpecification is = (InheritanceSpecification)parent;
                    Type t = getSourceInfo().getType(tr);
                    if (t instanceof TypeParameterDeclaration) {
                        continue; // will be taken care of by ResolveSingleGenericType
                    }
                    if (tr.getTypeArguments() == null) {
                        continue;
                    }
                    // need to introduce type cast in every (inherited) method which
                    // is not defined incurrent CU and has generic return type
                    // TODO fields !!
                    List<? extends Method> ml =
                        ((InheritanceSpecification) parent).getParent().getAllMethods();
                    for (Method m : ml) {
                        if (m instanceof MethodInfo
                                || UnitKit.getCompilationUnit((MethodDeclaration) m) != cu) {
                            p = new ResolveMethodReturnType(getServiceConfiguration(), m);
                            if (p.analyze() != IDENTITY) {
                                trParts.add(p);
                            }
                        }
                    }
                    stuffToBeRemoved.addAll(tr.getTypeArguments());
                    continue;
                } else if (parent instanceof MethodReference
                        && parent.getASTParent() instanceof MethodReference) {
                    // reference to static member
                    Method m = getSourceInfo().getMethod((MethodReference) parent.getASTParent());
                    if (m instanceof MethodInfo
                            || UnitKit.getCompilationUnit((MethodDeclaration) m) != cu) {
                        p = new ResolveMethodReturnType(getServiceConfiguration(), m);
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
                if (p.analyze() != IDENTITY) {
                    trParts.add(p);
                }
            } else if (pe instanceof New) {
                New n = (New) pe;
                if (n.getTypeReference().getTypeArguments() != null) {
                    stuffToBeRemoved.addAll(n.getTypeReference().getTypeArguments());
                }
            }
        }
        if (parts.size() == 0 && stuffToBeRemoved.size() == 0) {
            return setProblemReport(IDENTITY);
        }
        return super.analyze();
    }

    @Override
    public void transform() {
        super.transform();
        for (int i = parts.size() - 1; i >= 0; i--) {
            parts.get(i).transform();
        }
        for (TwoPassTransformation tp : trParts) {
            tp.transform();
        }
        for (ProgramElement pe : stuffToBeRemoved) {
            if (pe.getASTParent().getIndexOfChild(pe) != -1) {
                detach(pe);
            }
        }
    }

    private static class IntroduceCast {
        final Expression toBeCasted;
        final TypeReference castedType;

        IntroduceCast(Expression e, TypeReference tr) {
            this.toBeCasted = e;
            this.castedType = tr;
        }
    }

    private static class TypeParamRefReplacement {
        final TypeReference typeParamRef;
        final TypeReference replacement;

        TypeParamRefReplacement(TypeReference from, TypeReference to) {
            this.typeParamRef = from;
            this.replacement = to;
            replacement.setTypeArguments(null);
        }
    }

    public static class ResolveSingleGenericType extends TwoPassTransformation {
        private final TypeDeclaration td;
        private List<ProgramElement> stuffToBeRemoved;
        private List<IntroduceCast> casts;
        private List<TypeParamRefReplacement> typeParamReferences;

        ResolveSingleGenericType(CrossReferenceServiceConfiguration sc, TypeDeclaration td) {
            super(sc);
            this.td = td;
        }

        @Override
        public ProblemReport analyze() {
            List<TypeParameterDeclaration> typeParams = td.getTypeParameters();
            if (typeParams == null || typeParams.size() == 0) {
                return setProblemReport(IDENTITY);
            }

            stuffToBeRemoved = new ArrayList<>(100);
            casts = new ArrayList<>();
            typeParamReferences = new ArrayList<>();

            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();

            ResolveGenerics.analyze(getProgramFactory(), ci, typeParams, stuffToBeRemoved, casts,
                typeParamReferences);

            // now deal with type references using type arguments (no need to deal with raw types)
            List<TypeReference> trl = ci.getReferences(td);
            for (TypeReference tr : trl) {
                List<TypeArgumentDeclaration> typeArgs = tr.getTypeArguments();
                if (typeArgs == null || typeArgs.size() == 0) {
                    continue;
                }
                stuffToBeRemoved.addAll(typeArgs);
            }
            // remove type parameters
            stuffToBeRemoved.addAll(typeParams);

            return super.analyze();
        }

        @Override
        public void transform() {
            super.transform();
            if (getProblemReport() == IDENTITY) {
                return;
            }
            ProgramFactory f = getProgramFactory();
            for (IntroduceCast c : casts) {
                MiscKit.unindent(c.toBeCasted);
                if (!(c.toBeCasted.getASTParent() instanceof StatementContainer)) {
                    replace(c.toBeCasted, f.createParenthesizedExpression(
                        f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
                }
            }
            for (TypeParamRefReplacement t : typeParamReferences) {
                MiscKit.unindent(t.replacement);
                replace(t.typeParamRef, t.replacement);
            }
            for (ProgramElement tbr : stuffToBeRemoved) {
                if (tbr.getASTParent().getChildPositionCode(tbr) != -1) {
                    detach(tbr); // may not be part of model any more...
                }
                // TODO may this have any effect on undo operations ?
            }
            MiscKit.unindent(td);
        }
    }

    public static class ResolveGenericMethod extends TwoPassTransformation {
        private final MethodDeclaration md;
        private List<ProgramElement> stuffToBeRemoved;
        private List<IntroduceCast> casts;
        private List<TypeParamRefReplacement> typeParamReferences;

        public ResolveGenericMethod(CrossReferenceServiceConfiguration sc, MethodDeclaration md) {
            super(sc);
            this.md = md;
        }

        @Override
        public ProblemReport analyze() {
            List<TypeParameterDeclaration> typeParams = md.getTypeParameters();
            if (typeParams == null || typeParams.size() == 0) {
                return setProblemReport(IDENTITY);
            }

            ProgramFactory f = getProgramFactory();

            stuffToBeRemoved = new ArrayList<>(100);
            casts = new ArrayList<>();
            typeParamReferences = new ArrayList<>();

            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
            ResolveGenerics.analyze(f, ci, typeParams, stuffToBeRemoved, casts,
                typeParamReferences);

            // now deal with type references using type arguments (no need to deal with raw types)
            List<MemberReference> mrl = ci.getReferences(md);
            for (MemberReference memberReference : mrl) {
                MethodReference mr = (MethodReference) memberReference;
                List<TypeArgumentDeclaration> typeArgs = mr.getTypeArguments();
                if (typeArgs == null || typeArgs.size() == 0) {
                    continue;
                }
                stuffToBeRemoved.addAll(typeArgs);
            }
            // remove type parameters
            stuffToBeRemoved.addAll(typeParams);

            return super.analyze();
        }

        @Override
        public void transform() {
            super.transform();
            if (getProblemReport() == IDENTITY) {
                return;
            }
            ProgramFactory f = getProgramFactory();
            for (IntroduceCast c : casts) {
                MiscKit.unindent(c.toBeCasted);
                if (!(c.toBeCasted.getASTParent() instanceof StatementContainer)) {
                    replace(c.toBeCasted, f.createParenthesizedExpression(
                        f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
                }
            }
            for (TypeParamRefReplacement t : typeParamReferences) {
                MiscKit.unindent(t.replacement);
                replace(t.typeParamRef, t.replacement);
            }
            for (ProgramElement tbr : stuffToBeRemoved) {
                if (tbr.getASTParent().getChildPositionCode(tbr) != -1) {
                    detach(tbr); // may not be part of model any more...
                }
                // TODO may this have any effect on undo operations ?
            }
            MiscKit.unindent(md);
        }
    }

    public static class ResolveMethodReturnType extends TwoPassTransformation {
        private final Method md;
        private TypeReference tr;
        private List<ProgramElement> stuffToBeRemoved;
        private List<IntroduceCast> casts;

        public ResolveMethodReturnType(CrossReferenceServiceConfiguration sc, Method md) {
            super(sc);
            this.md = md;
            if (md instanceof MethodDeclaration) {
                this.tr = ((MethodDeclaration) md).getTypeReference();
            }
        }

        @Override
        public ProblemReport analyze() {
            Type returnType = md.getReturnType();
            if (!(returnType instanceof ParameterizedType)
                    && !(returnType instanceof TypeParameter)) {
                return IDENTITY;
            }
            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();

            stuffToBeRemoved = new ArrayList<>();
            if (md instanceof MethodDeclaration) {
                if (tr.getTypeArguments() != null) {
                    stuffToBeRemoved.addAll(tr.getTypeArguments());
                }
            }

            casts = new ArrayList<>();

            List<MemberReference> mrl = ci.getReferences(md);
            for (MemberReference memberReference : mrl) {
                MethodReference vr = (MethodReference) memberReference;
                NonTerminalProgramElement parent = vr.getASTParent();

                while (parent instanceof MethodReference) {
                    Type ty = ci.getType((MethodReference) parent);
                    if (!(ty instanceof ClassType)) {
                        break;
                    }
                    if (!(ty instanceof TypeParameter)) {
                        casts.add(new IntroduceCast(vr,
                            TypeKit.createTypeReference(ci, getSourceInfo().getType(vr), parent)));
                    }
                    parent = ((MethodReference) parent).getReferenceSuffix();
                }
            }
            return super.analyze();
        }

        @Override
        public void transform() {
            ProgramFactory f = getProgramFactory();
            for (IntroduceCast c : casts) {
                MiscKit.unindent(c.toBeCasted);
                if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1
                        && !(c.toBeCasted.getASTParent() instanceof StatementContainer)) {
                    replace(c.toBeCasted, f.createParenthesizedExpression(
                        f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
                }
            }
            if (md instanceof MethodDeclaration) {
                for (ProgramElement pe : stuffToBeRemoved) {
                    if (pe.getASTParent().getIndexOfChild(pe) != -1) {
                        detach(pe);
                    }
                }
            }
        }
    }

    public static class ResolveSingleVariableDeclaration extends TwoPassTransformation {
        private final VariableDeclaration vd;
        private final TypeReference tr;
        private List<ProgramElement> stuffToBeRemoved;
        private List<IntroduceCast> casts;

        public ResolveSingleVariableDeclaration(CrossReferenceServiceConfiguration sc,
                VariableDeclaration vd) {
            super(sc);
            this.vd = vd;
            this.tr = vd.getTypeReference();
        }

        @Override
        public ProblemReport analyze() {
            if (tr.getTypeArguments() == null || tr.getTypeArguments().size() == 0) {
                return IDENTITY;
            }

            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();

            stuffToBeRemoved = new ArrayList<>();
            stuffToBeRemoved.addAll(tr.getTypeArguments());

            casts = new ArrayList<>();

            for (int i = 0, s = vd.getVariables().size(); i < s; i++) {
                VariableSpecification vs = vd.getVariables().get(i);
                List<? extends VariableReference> vrl = ci.getReferences(vs);
                for (VariableReference vr : vrl) {
                    NonTerminalProgramElement parent = vr.getASTParent();

                    while (parent instanceof MethodReference) {
                        Type ty = ci.getType((MethodReference) parent);
                        if (!(ty instanceof ClassType)) {
                            break;
                        }
                        if (!(ty instanceof TypeParameter)) {
                            casts.add(new IntroduceCast((MethodReference) parent,
                                TypeKit.createTypeReference(ci, ty, parent)));
                        }
                        parent = ((MethodReference) parent).getReferenceSuffix();
                    }
                }
            }
            return super.analyze();
        }

        @Override
        public void transform() {
            ProgramFactory f = getProgramFactory();
            for (IntroduceCast c : casts) {
                MiscKit.unindent(c.toBeCasted);
                if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1
                        && !(c.toBeCasted.getASTParent() instanceof StatementContainer)) {
                    replace(c.toBeCasted, f.createParenthesizedExpression(
                        f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
                }
            }
            for (ProgramElement pe : stuffToBeRemoved) {
                if (pe.getASTParent().getIndexOfChild(pe) != -1) {
                    detach(pe);
                }
            }
        }
    }
}
