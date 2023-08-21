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
import recoder.convenience.TreeWalker;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.Operator;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.reference.ArrayReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.statement.Assert;
import recoder.java.statement.Return;
import recoder.java.statement.Switch;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;

/**
 * traverses a (sub)tree and replaces (un-)boxing conversions with explicit conversions.
 *
 * @author Tobias Gutzmann
 * @since 0.80
 */
public class ResolveBoxing extends TwoPassTransformation {

    private final NonTerminalProgramElement root;
    private final List<Expression> toUnbox = new ArrayList<>();
    private final List<Expression> toBox = new ArrayList<>();

    /**
     * @param sc
     * @param root
     */
    public ResolveBoxing(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    @Override
    public ProblemReport analyze() {
        SourceInfo si = getServiceConfiguration().getSourceInfo();
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof Expression) {
                NonTerminalProgramElement parent = pe.getASTParent();
                Expression e = (Expression) pe;
                Type t = si.getType(e);
                Type tt = null; // target type
                if (parent instanceof MethodReference) {
                    // find out if boxing has been used
                    MethodReference mr = (MethodReference) parent;
                    Method m = si.getMethod(mr);
                    if (mr.getArguments() != null) {
                        int idx = mr.getArguments().indexOf(e);
                        // TODO does not work with var arg!!! Will throw exception !!!
                        if (idx != -1) {
                            tt = m.getSignature().get(idx);
                        }
                        // otherwise, expression is not used as an argument
                        // but e.g. as a reference prefix
                    }
                } else if (parent instanceof Operator) {
                    Operator op = (Operator) parent;
                    if (op.getArity() == 2) {
                        Type target = si.getType(op);
                        if (target instanceof PrimitiveType && e instanceof ClassType) {
                            // unboxing needed
                            tt = target;
                        }
                    } else if (op.getArity() == 3) {
                        /*
                         * if target is an intersection type, we always box for java 4
                         * compatibility. But don't box first argument (condition)!
                         */
                        if (op.getArguments().get(0) != e) {

                            Type target = si.getType(op);
                            if (target instanceof IntersectionType) {
                                toBox.add(e);
                            }
                            /*
                             * in case it's not an intersection, but just a "most common" type: /*
                             * example: (true ? "hello, world" : 5).getClass();
                             */
                            if (t instanceof PrimitiveType && target instanceof ClassType) {
                                toBox.add(e);
                            }
                        }

                    }
                    /*
                     * else arity == 1 => nothing to do, because stuff like i++, where i is of type
                     * java.lang.Integer, is not allowed.
                     */
                } else if (parent instanceof VariableSpecification) {
                    tt = ((VariableSpecification) parent).getType();
                } else if (parent instanceof Return) {
                    tt = si.getType(MiscKit.getParentMemberDeclaration(parent));
                } else if (parent instanceof Switch) {
                    if (t instanceof ClassType && !((ClassType) t).isEnumType()) {
                        toUnbox.add(e);
                    }
                } else if (parent instanceof Assert) {
                    if (t instanceof ClassType) {
                        toUnbox.add(e);
                    }
                } else if (parent instanceof ArrayReference) {
                    if (t instanceof ClassType) {
                        toUnbox.add(e);
                    }
                } else if (parent instanceof ArrayInitializer) {
                    tt = ((ArrayType) si.getType((ArrayInitializer) parent)).getBaseType();
                }
                if (tt != null) {
                    if (tt instanceof ClassType && t instanceof PrimitiveType) {
                        toBox.add(e);
                    } else if (tt instanceof PrimitiveType && t instanceof ClassType) {
                        toUnbox.add(e);
                    }
                }
            }
        }
        return super.analyze();
    }

    @Override
    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        SourceInfo si = getServiceConfiguration().getSourceInfo();
        NameInfo ni = getServiceConfiguration().getNameInfo();
        for (Expression e : toBox) {
            Identifier id;
            PrimitiveType t = (PrimitiveType) si.getType(e);
            if (t == ni.getBooleanType()) {
                id = f.createIdentifier("Boolean");
            } else if (t == ni.getByteType()) {
                id = f.createIdentifier("Byte");
            } else if (t == ni.getShortType()) {
                id = f.createIdentifier("Short");
            } else if (t == ni.getCharType()) {
                id = f.createIdentifier("Character");
            } else if (t == ni.getIntType()) {
                id = f.createIdentifier("Integer");
            } else if (t == ni.getLongType()) {
                id = f.createIdentifier("Long");
            } else if (t == ni.getFloatType()) {
                id = f.createIdentifier("Float");
            } else if (t == ni.getDoubleType()) {
                id = f.createIdentifier("Double");
            } else {
                throw new Error();
            }
            TypeReference tr = f.createTypeReference(id);
            MethodReference replacement = f.createMethodReference(tr, f.createIdentifier("valueOf"),
                new ASTArrayList<>(e.deepClone()));
            replace(e, replacement);
        }
        for (Expression e : toUnbox) {
            Identifier id;
            ClassType t = (ClassType) si.getType(e);
            if (t == ni.getJavaLangBoolean()) {
                id = f.createIdentifier("booleanValue");
            } else if (t == ni.getJavaLangByte()) {
                id = f.createIdentifier("byteValue");
            } else if (t == ni.getJavaLangShort()) {
                id = f.createIdentifier("shortValue");
            } else if (t == ni.getJavaLangCharacter()) {
                id = f.createIdentifier("charValue");
            } else if (t == ni.getJavaLangInteger()) {
                id = f.createIdentifier("intValue");
            } else if (t == ni.getJavaLangLong()) {
                id = f.createIdentifier("longValue");
            } else if (t == ni.getJavaLangFloat()) {
                id = f.createIdentifier("floatValue");
            } else if (t == ni.getJavaLangDouble()) {
                id = f.createIdentifier("doubleValue");
            } else {
                throw new Error("cannot unbox type " + t.getFullName() + " (" + t.getClass() + ")");
            }
            ReferencePrefix rp;
            if (e instanceof ParenthesizedExpression) {
                rp = (ParenthesizedExpression) e.deepClone();
            } else {
                rp = f.createParenthesizedExpression(e.deepClone());
            }
            MethodReference replacement = f.createMethodReference(rp, id);
            replace(e, replacement);
        }
    }


}
