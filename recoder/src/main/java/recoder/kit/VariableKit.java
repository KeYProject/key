/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.TreeWalker;
import recoder.java.Identifier;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.VariableScope;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.FieldReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

/**
 * this class implements basic functions for type reference handling.
 *
 * @author Uwe Assmann
 * @author Andreas Ludwig
 * @author Rainer Neumann
 */
public class VariableKit {

    private VariableKit() {
        super();
    }

    /**
     * creates a new variable name which does not exist within the given scope using the given
     * <tt>guess</tt> as a name base.
     *
     * @param si the source information service to be used
     * @param context the element that defines the scope
     * @param guess the variable name to be used if possible. If a variable with that name already
     *        exists, the method uses suffix numbers.
     * @return a valid variable name within the given scope.
     */
    public static String createValidVariableName(SourceInfo si, ProgramElement context,
            String guess) {
        Debug.assertNonnull(si, context, guess);
        String result = guess;
        int i = 0;
        Set vars = collectInnerVariables(context);
        while (si.getVariable(result, context) != null || vars.contains(result)) {
            result = guess + (i++);
        }
        return result;
    }

    /**
     * creates a new variable name which does not exist within the given scope.
     *
     * @param si the source information service to be used
     * @param context the element that defines the scope
     * @return a valid variable name within the given scope.
     */
    public static String createValidVariableName(SourceInfo si, ProgramElement context) {
        return createValidVariableName(si, context, "_hvar_");
    }

    /**
     * Creates a declaration for a new variable with the given type and a name similar to the given
     * guess.
     *
     * @param sc the service configuration to be used
     * @param sde the element that defines the scope
     * @param guess the variable name to be used if possible. If a variable with that name already
     *        exists, the method uses suffix numbers.
     * @param t the type of the variable to be declared.
     * @return a valid variable name within the given scope.
     * @deprecated use createNewVariableName instead
     */
    @Deprecated
    public static VariableDeclaration createVariableDeclaration(ServiceConfiguration sc,
            ProgramElement context, Type t, String guess) {
        Debug.assertNonnull(sc, context, t);
        String vname = createValidVariableName(sc.getSourceInfo(), context, guess);

        ProgramFactory pf = sc.getProgramFactory();
        TypeReference prefix = TypeKit.createTypeReference(pf, t);
        Identifier id = pf.createIdentifier(vname);
        return pf.createLocalVariableDeclaration(prefix, id);
    }

    /**
     * Creates a new local variable declaration with the given type and a new artificial name.
     *
     * @param sc the service configuration to be used.
     * @param context the element that defines the scope.
     * @param t the type of the variable to be declared.
     * @return a valid variable name within the given scope.
     */
    public static VariableDeclaration createVariableDeclaration(ServiceConfiguration sc,
            ProgramElement context, Type t) {
        Debug.assertNonnull(sc, context, t);
        String varName = getNewVariableName(sc.getSourceInfo(), t, context);
        ProgramFactory f = sc.getProgramFactory();
        TypeReference prefix = TypeKit.createTypeReference(f, t);
        Identifier id = f.createIdentifier(varName);
        return f.createLocalVariableDeclaration(prefix, id);
    }

    /**
     * Create a reference to the first variable in a variable declaration. If there are multiple
     * declarations (as in "int i = 0, j = 0;"), only the first one is used. This is no problem with
     * e.g. ParameterDeclarations.
     *
     * @param decl the declaration to create a reference for.
     * @return a new variable reference to the first specification in the given declaration.
     */
    public static VariableReference createVariableReference(VariableDeclaration decl) {

        ProgramFactory factory = decl.getFactory();
        String n = decl.getVariables().get(0).getName();
        return factory.createVariableReference(factory.createIdentifier(n));
    }

    // returns a set of local variable names declared within the scope of the
    // given context and of inner scopes.
    private static Set<String> collectInnerVariables(ProgramElement context) {
        Set<String> result = new HashSet<>();
        while (context != null && !(context instanceof VariableScope)) {
            context = context.getASTParent();
        }
        if (context != null) {
            TreeWalker tw = new TreeWalker(context);
            while (tw.next()) {
                if (tw.getProgramElement() instanceof Variable) {
                    result.add(((Variable) tw.getProgramElement()).getName());
                }
            }
        }
        return result;
    }

    /**
     * Query method that finds a name for a new variable with the given type.
     *
     * @param si the source info service.
     * @param type the type of the variable to be declared.
     * @param context the future context of the variable (defines its scope).
     * @return a variable name that is valid in the given context.
     */
    public static String getNewVariableName(SourceInfo si, Type type, ProgramElement context) {
        Debug.assertNonnull(si, type, context);
        NameGenerator generator = new NameGenerator(type);
        Set vars = collectInnerVariables(context);
        String result;
        for (result = generator.getNextCandidate(); si.getVariable(result, context) != null
                || vars.contains(result); result = generator.getNextCandidate()) {
            // logic contained in loop control
        }
        return result;
    }

    /**
     * Query method that finds names for new variables with the given types.
     *
     * @param si the source info service.
     * @param types the types of the variables to be declared.
     * @param context the future context of the variables.
     * @return an array of disjoint variable names that are all valid in the given context.
     */
    public static String[] getNewVariableNames(SourceInfo si, Type[] types,
            ProgramElement context) {
        Debug.assertNonnull(si, types, context);
        // speed up things a little bit
        while (!(context instanceof VariableScope)) {
            context = context.getASTParent();
        }
        Set<String> others = collectInnerVariables(context);
        String[] results = new String[types.length];
        for (int i = 0; i < results.length; i += 1) {
            NameGenerator generator = new NameGenerator(types[i]);
            String vname;
            do {
                vname = generator.getNextCandidate();
            } while (si.getVariable(vname, context) != null || others.contains(vname));
            results[i] = vname;
            others.add(vname);
        }
        return results;
    }

    /**
     * Transformation that renames a variable and all known references to it. The new name should
     * not hide another variable.
     *
     * @param ch the change history (may be <CODE>null</CODE>).
     * @param xr the cross referencer service.
     * @param var the variable specification to be renamed; may not be <CODE>
     *                null</CODE>.
     * @param newName the new name for the variable; may not be <CODE>null</CODE> and must denote a
     *        valid identifier name.
     * @return <CODE>true</CODE>, if a rename has been necessary, <CODE>
     * false</CODE> otherwise.
     * @deprecated replaced by recoder.kit.transformation.RenameVariable
     */
    @Deprecated
    public static boolean rename(ChangeHistory ch, CrossReferenceSourceInfo xr,
            VariableSpecification var, String newName) {
        Debug.assertNonnull(xr, var, newName);
        Debug.assertNonnull(var.getName());
        if (!newName.equals(var.getName())) {
            List<? extends VariableReference> refs = xr.getReferences(var);
            MiscKit.rename(ch, var, newName);
            for (int i = refs.size() - 1; i >= 0; i -= 1) {
                MiscKit.rename(ch, refs.get(i), newName);
            }
            return true;
        }
        return false;
    }

    /**
     * Factory method that creates a minimal qualified reference to the given variable (or field)
     * for the given context. Returns <CODE>null</CODE> if the variable is not accessible in the
     * given context, i.e. from a different type, or hidden by another local variable, or hidden by
     * another inherited field.
     *
     * @param si the source info service to be used.
     * @param v the variable to be referred to.
     * @param context the context to insert the variable reference later on.
     */
    public static VariableReference createVariableReference(SourceInfo si, Variable v,
            ProgramElement context) {
        Debug.assertNonnull(si, v, context);
        String varname = v.getName();
        ProgramFactory f = context.getFactory();
        Variable lookup = si.getVariable(varname, context);
        if (lookup == null) {
            return null;
        }
        if (lookup == v) {
            VariableReference res = f.createVariableReference(f.createIdentifier(varname));
            res.makeAllParentRolesValid();
            return res;
        }
        // hiding local variables with local variables is forbidden
        if (!(v instanceof Field)) {
            return null;
        }
        ClassType varClass = ((Field) v).getContainingClassType();
        TypeDeclaration ctxClass = MiscKit.getParentTypeDeclaration(context);
        TypeReference prefix = null;
        do {
            // see if it's a field covered by some local declarations
            if (varClass == ctxClass) {
                // access by "this.", then
                FieldReference res = f.createFieldReference(f.createIdentifier(varname));
                res.setReferencePrefix(f.createThisReference(prefix));
                res.makeAllParentRolesValid();
                return res;
            }
            // see if the field is inherited
            // we will have to do it manually as getAllFields does not
            // report hidden fields
            List<ClassType> sups = ctxClass.getAllSupertypes();
            both: for (int i = 1, s = sups.size(); i < s; i += 1) {
                ClassType sup = sups.get(i);
                List<? extends Field> flist = sup.getFields();
                for (Field candid : flist) {
                    if (varname.equals(candid.getName())) {
                        if (candid == v && si.isVisibleFor(candid, ctxClass)) {
                            // access by "super.", then
                            FieldReference res =
                                f.createFieldReference(f.createIdentifier(varname));
                            res.setReferencePrefix(f.createSuperReference(prefix));
                            res.makeAllParentRolesValid();
                            return res;
                        } else {
                            // there is no way to access a hidden inherited
                            // variable but there might be from an outer class
                            break both;
                        }
                    }
                }
            }
            ctxClass = ctxClass.getMemberParent();
            if (ctxClass != null) {
                // proceed with the outer reference
                prefix = TypeKit.createTypeReference(si, ctxClass, context);
            }
        } while (ctxClass != null);
        // if there is no outer class, we cannot access the variable
        return null;
    }

    /**
     * Query that retrieves all references to a given variable that are contained within the given
     * tree. The specified flag defines the strategy to use: either the cross reference information
     * is filtered, or the cross reference information is collected from the tree. The filtering
     * mode is faster if the tree contains more nodes than there are global references to the given
     * variable.
     *
     * @param xr the cross referencer to use.
     * @param v a variable.
     * @param root the root of an arbitrary syntax tree.
     * @param scanTree flag indicating the search strategy; if <CODE>true</CODE>, local cross
     *        reference information is build, otherwise the global cross reference information is
     *        filtered.
     * @return the list of references to the given variable in the given tree, can be empty but not
     *         <CODE>null</CODE>.
     * @since 0.63
     */
    public static List<VariableReference> getReferences(CrossReferenceSourceInfo xr, Variable v,
            NonTerminalProgramElement root, boolean scanTree) {
        Debug.assertNonnull(xr, v, root);
        List<VariableReference> result = new ArrayList<>();
        if (scanTree) {
            TreeWalker tw = new TreeWalker(root);
            while (tw.next(VariableReference.class)) {
                VariableReference vr = (VariableReference) tw.getProgramElement();
                if (xr.getVariable(vr) == v) {
                    result.add(vr);
                }
            }
        } else {
            List<? extends VariableReference> refs = xr.getReferences(v);
            for (VariableReference vr : refs) {
                if (MiscKit.contains(root, vr)) {
                    result.add(vr);
                }
            }
        }
        return result;
    }

    /**
     * Updating query that checks if the given field is a <CODE>
     * serialVersionUID</CODE> constant.
     *
     * @param ni the NameInfo service to use.
     * @param f the field to check.
     * @return <CODE>true</CODE> if the given field is a serial version UID of a type,
     *         <CODE>false</CODE> otherwise.
     */
    public static boolean isSerialVersionUID(NameInfo ni, Field f) {
        return (f.isStatic() && f.isFinal() && f.getType() == ni.getLongType()
                && f.getName().equals("serialVersionUID"));
    }

}
