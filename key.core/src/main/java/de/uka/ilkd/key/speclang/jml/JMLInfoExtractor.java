/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Helper class used by the JML translation. Provides methods that look for certain keywords (such
 * as "pure") in comments, and that help in desugaring such keywords.
 */
public final class JMLInfoExtractor {
    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Checks whether "comment" is a JML comment containing "key". see bugreport #1166
     */
    private static boolean checkFor(String key, String comment) {
        return comment.contains(key) && MiscTools.isJMLComment(comment);
    }


    /**
     * Checks whether one of the passed comments is a JML comment containing "key".
     */
    private static boolean checkFor(String key, ImmutableList<Comment> coms) {
        for (Comment c : coms) {
            if (checkFor(key, c.getText())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether one of the passed comments is a JML comment containing "key" and not *bad*.
     */
    private static boolean checkForNotContaining(String key, String bad,
            ImmutableList<Comment> coms) {
        for (Comment c : coms) {
            if (checkFor(key, c.getText()) && !c.getText().contains(bad)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks the passed comments for the spec math mode.
     */
    private static SpecMathMode checkForSpecMathMode(ImmutableList<Comment> comments) {
        // This is hacky but hard to do better
        // We exclude comments containing 'behaviour' since they can be from the method contract
        var specBigintMath = checkForNotContaining("spec_bigint_math", "behaviour", comments);
        var specSafeMath = checkForNotContaining("spec_safe_math", "behaviour", comments);
        var specJavaMath = checkForNotContaining("spec_java_math", "behaviour", comments);
        // Consistency: bigint > safe > java
        return specBigintMath ? SpecMathMode.BIGINT
                : (specSafeMath ? SpecMathMode.SAFE : (specJavaMath ? SpecMathMode.JAVA : null));
    }

    private static ImmutableList<Comment> getJMLComments(TypeDeclaration td) {
        ImmutableList<Comment> coms = ImmutableSLList.nil();

        // Either mod is attached to the declaration itself ...
        coms = coms.prepend(td.getComments());

        // ... or to a modifier ...
        for (Modifier m : td.getModifiers()) {
            coms = coms.prepend(m.getComments());
        }

        // ... or to the name
        if (td.getProgramElementName() != null) {
            coms = coms.prepend(td.getProgramElementName().getComments());
        }
        return coms;
    }

    private static ImmutableList<Comment> getJMLComments(MethodDeclaration method) {
        ImmutableList<Comment> coms = ImmutableSLList.nil();

        // Either mod is attached to the method itself ...
        Comment[] methodComments = method.getComments();
        if (methodComments.length > 0) {
            coms = coms.prepend(methodComments[methodComments.length - 1]);
        }

        // ... or to a modifier ...
        for (Modifier m : method.getModifiers()) {
            coms = coms.prepend(m.getComments());
        }

        // ... or to the return type ...
        if (!method.isVoid() && !(method instanceof ConstructorDeclaration)) {
            coms = coms.prepend(method.getTypeReference().getComments());
        }

        // ... or to 'void' ...
        if (method.getVoidComments() != null) {
            coms = coms.prepend(method.getVoidComments());
        }

        // ... or to the method name
        coms = coms.prepend(method.getProgramElementName().getComments());
        return coms;
    }

    /**
     * Parses a modifiers of a method
     *
     * @param methodDeclaration the method declaration
     * @return modifiers
     */
    public static MethodDeclaration.JMLModifiers parseMethod(MethodDeclaration methodDeclaration) {
        var comments = getJMLComments(methodDeclaration);

        var pure = checkFor("pure", comments);
        var strictlyPure = checkFor("strictly_pure", comments);
        var helper = checkFor("helper", comments);
        var specMathMode = checkForSpecMathMode(comments);

        return new MethodDeclaration.JMLModifiers(pure, strictlyPure, helper, specMathMode);
    }

    private static boolean hasJMLModifier(MethodDeclaration pm, String mod) {
        var coms = getJMLComments(pm);
        return checkFor(mod, coms);
    }


    /**
     * Extracts the list of comments for a given field. The comments should usually be modifiers.
     *
     * @param fieldName
     * @param td
     * @return
     */
    private static ImmutableList<Comment> extractFieldModifiers(String fieldName,
            TypeDeclaration td) {
        ImmutableList<Comment> comments = ImmutableSLList.nil();
        FieldDeclaration fd = null;
        int position = 0;

        for (final MemberDeclaration md : td.getMembers()) {
            if (md instanceof FieldDeclaration) {
                FieldDeclaration tmp = (FieldDeclaration) md;
                ImmutableArray<FieldSpecification> aofs = tmp.getFieldSpecifications();
                for (int j = 0; j < aofs.size(); j++) {
                    if (aofs.get(j).getProgramName().equals(fieldName)) {
                        fd = tmp;
                        position = j;
                    }
                }
            }
        }

        if (fd == null) {
            // Field not found
            return comments;
        }

        comments = comments.prepend(fd.getComments());
        comments = comments.prepend(fd.getTypeReference().getComments());
        comments = comments.prepend(fd.getFieldSpecifications().get(position).getComments());

        for (Modifier mod : fd.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }
        return comments;
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public static boolean hasJMLModifier(FieldDeclaration fd, String mod) {
        ImmutableList<Comment> coms = ImmutableSLList.nil();

        // Either mod is attached to the declaration itself ...
        coms = coms.prepend(fd.getComments());

        // ... or to a modifier ...
        for (Modifier m : fd.getModifiers()) {
            coms = coms.prepend(m.getComments());
        }

        // ... or to the type
        coms = coms.prepend(fd.getTypeReference().getComments());

        return checkFor(mod, coms);
    }


    /**
     * Returns true iff the given type is specified as pure, i.e. all methods and constructors are
     * by default specified "pure"
     * <p>
     * If t is not a reference type, false is returned.
     */
    public static boolean isPureByDefault(KeYJavaType t) {
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else {
            return ((TypeDeclaration) t.getJavaType()).getJmlModifiers().pure;
        }
    }

    /**
     * Returns true iff the given type is specified as pure, i.e. all methods and constructors are
     * by default specified "strictly_pure"
     * <p>
     * If t is not a reference type, false is returned.
     */
    public static boolean isStrictlyPureByDefault(KeYJavaType t) {
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else {
            return ((TypeDeclaration) t.getJavaType()).getJmlModifiers().strictlyPure;
        }
    }


    /**
     * Returns true if the given type is specified as nullable, i.e. all fields and method
     * parameters are by default specified "nullable"
     * <p>
     * If t is not a reference type, false is returned.
     */
    public static boolean isNullableByDefault(KeYJavaType t) {
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else {
            return ((TypeDeclaration) t.getJavaType()).getJmlModifiers().nullableByDefault;
        }
    }

    /**
     * Parses modifiers of a type
     *
     * @param td the type declaration
     * @return modifiers
     */
    public static TypeDeclaration.JMLModifiers parseClass(TypeDeclaration td) {
        var comments = getJMLComments(td);

        var strictlyPure = checkFor("strictly_pure", comments);
        var pure = checkFor("pure", comments);
        var nullableByDefault = checkFor("nullable_by_default", comments);
        var specMathMode = checkForSpecMathMode(comments);

        return new TypeDeclaration.JMLModifiers(strictlyPure, pure, nullableByDefault,
            specMathMode);
    }

    /**
     * Returns true, if <tt>containingClass</tt> is a reference Type and has a field declaration
     * with name <tt>fieldName</tt>, which is explicitly or implicitly declared "nullable"
     */
    public static boolean isNullable(String fieldName, TypeDeclaration td) {

        ImmutableList<Comment> comments = extractFieldModifiers(fieldName, td);
        if (comments.isEmpty()) {
            return false;
        }

        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);

        if (!non_null && !nullable) {
            return td.getJmlModifiers().nullableByDefault;
        } else {
            return nullable;
        }
    }


    /**
     * Returns true iff the <code>pos</code>-th parameter of the given method is declared "nullable"
     * (implicitly or explicitly).
     */
    public static boolean parameterIsNullable(IProgramMethod pm, int pos) {
        MethodDeclaration md = pm.getMethodDeclaration();
        ParameterDeclaration pd = md.getParameterDeclarationAt(pos);

        return parameterIsNullable(pm, pd);
    }


    /**
     * Returns true iff the parameter of the given method is declared "nullable" (implicitly or
     * explicitly). Warning: weird things may happen if the parameter doesn't belong to the method.
     */
    public static boolean parameterIsNullable(IProgramMethod pm, ParameterDeclaration pd) {
        assert pm.getMethodDeclaration().getParameters().contains(pd)
                : "parameter " + pd + " does not belong to method declaration " + pm;
        ImmutableList<Comment> comments = ImmutableSLList.nil();
        comments = comments.prepend(pd.getComments());
        comments = comments.prepend(pd.getTypeReference().getComments());
        comments = comments.prepend(pd.getVariableSpecification().getComments());
        for (Modifier mod : pd.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }

        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);

        if (!non_null && !nullable) {
            return isNullableByDefault(pm.getContainerType());
        } else {
            return nullable;
        }
    }


    public static boolean resultIsNullable(IProgramMethod pm) {
        MethodDeclaration md = pm.getMethodDeclaration();

        ImmutableList<Comment> comments = ImmutableSLList.nil();
        for (Modifier mod : md.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }
        if (!pm.isVoid() && !pm.isConstructor()) {
            comments = comments.prepend(md.getTypeReference().getComments());
        }
        Comment[] methodComments = md.getComments();
        if (methodComments.length > 0) {
            comments = comments.prepend(methodComments[methodComments.length - 1]);
        }

        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);

        if (!non_null && !nullable) {
            return isNullableByDefault(pm.getContainerType());
        } else {
            return nullable;
        }
    }


    /**
     * Returns true iff the given method is specified "pure".
     */
    public static boolean isPure(IProgramMethod pm) {
        return pm.getMethodDeclaration().getJmlModifiers().pure
                || isPureByDefault(pm.getContainerType());
    }


    /**
     * Returns true iff the given method is specified "helper".
     */
    public static boolean isHelper(IProgramMethod pm) {
        return pm.getMethodDeclaration().getJmlModifiers().helper;
    }

    /**
     * Returns true iff the given method is specified "strictly_pure" or the containing type is
     * specified so.
     */
    public static boolean isStrictlyPure(IProgramMethod pm) {
        return pm.getMethodDeclaration().getJmlModifiers().strictlyPure
                || isStrictlyPureByDefault(pm.getContainerType());
    }

    /**
     * Returns the spec math mode of this type
     */
    @Nullable
    public static SpecMathMode getSpecMathMode(@Nonnull KeYJavaType t) {
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return null;
        } else {
            return ((TypeDeclaration) t.getJavaType()).getJmlModifiers().specMathMode;
        }
    }

    @Nonnull
    private static SpecMathMode modeOrDefault(@Nullable SpecMathMode mode) {
        return mode == null ? SpecMathMode.defaultMode() : mode;
    }

    /**
     * Returns the spec math mode of this type or the default
     */
    @Nonnull
    public static SpecMathMode getSpecMathModeOrDefault(@Nonnull KeYJavaType t) {
        return modeOrDefault(getSpecMathMode(t));
    }

    /**
     * Returns the spec math mode of this method
     */
    @Nullable
    public static SpecMathMode getSpecMathMode(@Nonnull IProgramMethod pm) {
        var methodMode = pm.getMethodDeclaration().getJmlModifiers().specMathMode;
        return methodMode != null ? methodMode : getSpecMathMode(pm.getContainerType());
    }

    /**
     * Returns the spec math mode of this method
     */
    @Nonnull
    public static SpecMathMode getSpecMathModeOrDefault(@Nonnull IProgramMethod pm) {
        return modeOrDefault(getSpecMathMode(pm));
    }
}
