/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.removegenerics;

import java.util.Collection;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
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
 * This is the base class to all transformations used in the generics removal process.
 * <p>
 * It allows 2 things: 1) calculating the target type of a type (which is the type when type
 * variables are no longer) and 2) to print out debug info.
 * <p>
 * String creation is a little tedious in recoder so {@link #toString(Object)} does a lot of it.
 *
 * @author MU
 */
public class GenericResolutionTransformation extends TwoPassTransformation {

    // allow debug output
    public static boolean DEBUG_OUTPUT = Boolean.getBoolean("resolvegen.verbose");
    private static final Logger LOGGER =
        LoggerFactory.getLogger(GenericResolutionTransformation.class);

    public GenericResolutionTransformation() {
        super();
    }

    public GenericResolutionTransformation(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    /**
     * get the type of the reference that it will have in a generic-free environment. If the
     * expression once had type <code>V</code> for some (unbound) type variable it will then have
     * <code>java.lang.Object</code> etc.
     *
     * @param t the type to be resolved
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
         * it might be necessary to do the following block more than once in a situation like:
         * G&lt;A, B extends A&gt; where B would be replaced by A, which needs to be resolved to
         * Object.
         */
        while (t instanceof TypeParameter) {
            changed = true;
            TypeParameter typeParameter = (TypeParameter) t;
            int boundNo = typeParameter.getBoundCount();
            if (boundNo == 0) {
                t = getNameInfo().getJavaLangObject();
                if (t == null) {
                    throw new IllegalStateException("java.lang.Object not known");
                }
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
     * if the global debug flag {@link #DEBUG_OUTPUT} is set to true print out a message.
     * <p>
     * First the message-head is printed followed by a ':', followed by a ;-separated list of the
     * arguments. Each argument is converted to a string using the {@link #toString(Object)}.
     *
     * @param msg the message's head
     * @param arg 0 or more objects that will be expanded to a ;-separated list after the message
     */

    public static void debugOut(String msg, Object... arg) {
        if (DEBUG_OUTPUT) {
            var args = new StringBuilder();
            if (arg.length > 0) {
                args.append(":");
                for (int i = 1; i < arg.length; i++) {
                    args.append("; ").append(toString(arg[i]));
                }
            }
            LOGGER.debug(msg + args);
        }
    }

    /**
     * convert an object to a String.
     * <p>
     * For some classes {@link Object#toString()} is lame, so that the following classes are caught
     * here:
     * <ul>
     * <li>{@link MethodDeclaration}
     * <li>{@link NamedModelElement}
     * <li>{@link Collection} - which handle each element with toString</li> Anything else will be
     * transoformed using {@link Object#toString()}.
     *
     * @param object the object to be transformed, may be null
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
            } else {
                return name;
            }
        }

        if (object instanceof Collection<?>) {
            StringBuilder ret = new StringBuilder("[ ");
            Collection<?> coll = (Collection<?>) object;
            for (Object o : coll) {
                ret.append(toString(o)).append(" ");
            }
            return ret + "]";
        }

        if (object == null) {
            return "(null)";
        }

        return object.toString();
    }

}
