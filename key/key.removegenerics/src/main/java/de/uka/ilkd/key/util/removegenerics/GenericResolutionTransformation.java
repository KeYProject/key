// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.removegenerics;

import java.util.Collection;

import recoder.CrossReferenceServiceConfiguration;
import recoder.NamedModelElement;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.Type;
import recoder.abstraction.TypeParameter;
import recoder.java.NamedProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.kit.TwoPassTransformation;

/**
 * This is the base class to all transformations used in the generics removal
 * process.
 * 
 * It allows 2 things: 1) calculating the target type of a type (which is the
 * type when type variables are no longer) and 2) to print out debug info.
 * 
 * String creation is a little tedious in recoder so {@link #toString(Object)}
 * does a lot of it.
 * 
 * @author MU
 * 
 */
public class GenericResolutionTransformation extends TwoPassTransformation {

    // allow debug output
    public static boolean DEBUG_OUTPUT = Boolean.getBoolean("resolvegen.verbose");

    public GenericResolutionTransformation() {
        super();
    }

    public GenericResolutionTransformation(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    /**
     * get the type of the reference that it will have in a generic-free
     * environment. If the expression once had type <code>V</code> for some
     * (unbound) type variable it will then have <code>java.lang.Object</code>
     * etc.
     * 
     * @param t
     *            the type to be resolved
     * @return the coresponding type in the generic-free environment
     */
    protected Type targetType(Type t) {
        int dimension = 0;
        boolean changed = false;
        Type origType = t;

        while (t instanceof ArrayType) {
            t = ((ArrayType) t).getBaseType();
            dimension++;
        }

        if (t instanceof ParameterizedType) {
            t = ((ParameterizedType) t).getGenericType();
            changed = true;
        }

        /*
         * it might be necessary to do the following block more than once in a
         * situation like: G&lt;A, B extends A&gt; where B would be replaced by A,
         * which needs to be resolved to Object.
         */
        while (t instanceof TypeParameter) {
            changed = true;
            TypeParameter typeParameter = (TypeParameter) t;
            int boundNo = typeParameter.getBoundCount();
            if (boundNo == 0) {
                t = getNameInfo().getJavaLangObject();
                if (t == null)
                    throw new RuntimeException("java.lang.Object not known");
            } else {
                String bound = typeParameter.getBoundName(0);
                if (typeParameter instanceof TypeParameterDeclaration) {
                    // TP - Declaration needs to know context (bound may rely on
                    // imports)
                    TypeParameterDeclaration tdecl = (TypeParameterDeclaration) typeParameter;
                    t = getSourceInfo().getType(bound, tdecl);
                } else {
                    // TP - Info from Class file is always complete (I hope)
                    t = getNameInfo().getType(bound);
                }
            }
        }

        if (changed) {
            if (dimension > 0) {
                t = getNameInfo().createArrayType(t, dimension);
            }
            return t;
        } else {
            return origType;
        }
    }

    /**
     * if the global debug flag {@link #DEBUG_OUTPUT} is set to true print out a
     * message.
     * 
     * First the message-head is printed followed by a ':', followed by a
     * ;-separated list of the arguments. Each argument is converted to a string
     * using the {@link #toString(Object)}.
     * 
     * @param msg
     *            the message's head
     * @param arg
     *            0 or more objects that will be expanded to a ;-separated list
     *            after the message
     */

    public static void debugOut(String msg, Object... arg) {
        if (DEBUG_OUTPUT) {
            System.out.print(msg);
            if (arg.length > 0) {
                System.out.print(": " + toString(arg[0]));
                for (int i = 1; i < arg.length; i++)
                    System.out.print("; " + toString(arg[i]));
            }
            System.out.println();
        }
    }

    /**
     * convert an object to a String.
     * 
     * For some classes {@link Object#toString()} is lame, so that the following
     * classes are caught here:
     * <ul>
     * <li> {@link MethodDeclaration}
     * <li> {@link NamedModelElement}
     * <li> {@link Collection} - which handle each element with toString </li>
     * Anything else will be transoformed using {@link Object#toString()}.
     * 
     * @param object
     *            the object to be transformed, may be null
     * @return a String representing the object.
     */
    public static String toString(Object object) {

        if (object instanceof MethodDeclaration) {
            MethodDeclaration md = (MethodDeclaration) object;
            return md.getFullName() + toString(md.getSignature());
        }

        if (object instanceof NamedModelElement) {
            NamedModelElement ne = (NamedModelElement) object;
            String name = ne.getName();
            if (object instanceof NamedProgramElement) {
                ProgramElement parent = ((NamedProgramElement) ne).getASTParent();
                if (parent instanceof NamedModelElement) {
                    NamedModelElement p = (NamedModelElement) parent;
                    return p.getName() + "::" + name;
                }
            } else
                return name;
        }

        if (object instanceof Collection<?>) {
            String ret = "[ ";
            Collection<?> coll = (Collection<?>) object;
            for (Object o : coll) {
                ret += toString(o) + " ";
            }
            return ret + "]";
        }

        if (object == null)
            return "(null)";

        return object.toString();
    }

}