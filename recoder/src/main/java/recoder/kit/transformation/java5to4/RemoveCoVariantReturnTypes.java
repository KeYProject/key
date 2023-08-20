/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.kit.MethodKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.DefaultSourceInfo;

/**
 * This transformation does not work yet!
 * <p>
 * <p>
 * uses type casts instead of co-variant return types. Does not work with primitive types yet.
 *
 * @author Tobias Gutzmann
 */
public class RemoveCoVariantReturnTypes extends TwoPassTransformation {
    private final NonTerminalProgramElement root;
    private List<Item> items;

    /**
     *
     */
    public RemoveCoVariantReturnTypes(CrossReferenceServiceConfiguration sc,
            NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    @Override
    public ProblemReport analyze() {
        this.items = new ArrayList<>();
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) pe;
                Type returnType = getSourceInfo().getReturnType(md);
                if (returnType == null || returnType instanceof PrimitiveType) {
                    continue;
                }
                List<Method> ml = MethodKit.getRedefinedMethods(md);
                if (ml.size() == 0) {
                    continue;
                }
                List<ClassType> ctml = new ArrayList<>(ml.size());
                for (Method method : ml) {
                    Type rt = getSourceInfo().getReturnType(method);
                    if (rt instanceof ClassType && !ctml.contains(rt)) {
                        ctml.add((ClassType) rt);
                    }
                }
                // this list is for debug purposes only:
                List<ClassType> ctml_copy = new ArrayList<>(ctml);
                TypeKit.removeCoveredSubtypes(getSourceInfo(), ctml);
                if (ctml.size() != 1) {
                    // System.err.println("<>1 common supertypes:");
                    // for (int i = 0; i < ctml.size(); i++) {
                    // System.err.println(ctml.getClassType(i).getFullName());
                    // }
                    // System.err.println("Was:");
                    // System.err.println(t.getFullName());
                    // System.err.println(md.getFullName());
                    // for (int i = 0; i < ctml_copy.size(); i++) {
                    // System.err.println(ctml_copy.getClassType(i).getFullName());
                    // }
                    // TODO look into this
                    if (ctml.size() == 0 && returnType instanceof ArrayType) {
                        continue;
                    }
                    throw new ModelException(); // semantic error in source program!
                }
                Type originalType = ctml.get(0);
                if (((DefaultSourceInfo) getSourceInfo()).containsTypeParameter(originalType)) {
                    // use class type bound instead
                    // TODO handle type args - grrrr
                    originalType = makeSomething(originalType);

                }
                if (originalType != returnType) {
                    // covariant return type...
                    TypeReference originalTypeReference =
                        TypeKit.createTypeReference(getProgramFactory(), originalType);
                    TypeReference castToReference =
                        TypeKit.createTypeReference(getProgramFactory(), returnType);
                    ASTList<TypeArgumentDeclaration> targs =
                        md.getTypeReference().getTypeArguments();
                    if (targs != null && targs.size() > 0) {
                        castToReference.setTypeArguments(targs.deepClone());
                    }
                    if (originalType instanceof ParameterizedType) {
                        recoder.abstraction.ParameterizedType pt =
                            (recoder.abstraction.ParameterizedType) originalType;
                        targs = TypeKit.makeTypeArgRef(getProgramFactory(), pt.getTypeArgs());
                        originalTypeReference.setTypeArguments(targs);
                    }
                    items.add(new Item(md, getCrossReferenceSourceInfo().getReferences(md),
                        originalTypeReference, castToReference));
                }
            }
        }
        return super.analyze();
    }

    private Type makeSomething(Type originalType) {
        if (originalType instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) originalType;
            ClassType baseType = (ClassType) makeSomething0(pt.getGenericType());
            ASTList<TypeArgumentDeclaration> targs =
                new ASTArrayList<>(pt.getTypeArgs().size());
            for (TypeArgument ta : pt.getTypeArgs()) {
                targs.add(makeSomething1(ta));
            }
            return new ParameterizedType(baseType, targs);
        } else {
            return makeSomething0(originalType);
        }
    }

    private Type makeSomething0(Type originalType) {
        if (!(originalType instanceof TypeParameter)) {
            return originalType;
        }
        TypeParameter tp = (TypeParameter) originalType;
        if (tp.getBoundCount() == 0) {
            originalType = getNameInfo().getJavaLangObject();
        } else {
            String tname = tp.getBoundName(0);
            originalType = getNameInfo().getClassType(tname);
            if (((ClassType) originalType).isInterface()) {
                originalType = getNameInfo().getJavaLangObject();
            }
            // TODO check - if not a class type, use interface instead ?!
        }
        return originalType;
    }

    private TypeArgumentDeclaration makeSomething1(TypeArgument ta) {
        TypeArgumentDeclaration res = new TypeArgumentDeclaration();
        res.setTypeReference(TypeKit.createTypeReference(getProgramFactory(), ta.getTypeName()));
        if (ta.getTypeArguments() != null && ta.getTypeArguments().size() > 0) {
            ASTList<TypeArgumentDeclaration> targs =
                new ASTArrayList<>(ta.getTypeArguments().size());
            for (TypeArgument t : ta.getTypeArguments()) {
                targs.add(makeSomething1(t));
            }
            res.getTypeReference().setTypeArguments(targs);
            res.getTypeReference().makeParentRoleValid();
        }
        return res;
    }

    @Override
    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        for (Item it : items) {
            replace(it.md.getTypeReference(), it.rt.deepClone());
            for (int i = 0; i < it.mrl.size(); i++) {
                MethodReference mr = (MethodReference) it.mrl.get(i);
                // TODO the parenthesis aren't always needed - find out, when !
                replace(mr, f.createParenthesizedExpression(
                    f.createTypeCast(mr.deepClone(), it.t.deepClone())));
            }
        }
    }

    private static class Item {
        final MethodDeclaration md;
        final List<MemberReference> mrl;
        final TypeReference t;
        final TypeReference rt;

        Item(MethodDeclaration md, List<MemberReference> mrl, TypeReference rt, TypeReference t) {
            this.md = md;
            this.mrl = mrl;
            this.rt = rt;
            this.t = t;
        }
    }

}
