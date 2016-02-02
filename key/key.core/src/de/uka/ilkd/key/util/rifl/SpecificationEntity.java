// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.util.rifl;

import java.util.Arrays;

/**
 * Program elements which may be named as sources or sinks in RIFL/Java.
 * Currently fields, method parameters, and method return values can be
 * named both sources and sinks.
 * 
 * @author bruns
 */
public abstract class SpecificationEntity {

    static enum Type { SOURCE, SINK }

    public static final class Field extends SpecificationEntity {

        public final String name;

        /**
         * Creates a new specification element for a field.
         * @param n name of the field
         * @param p package name of the class where the field is declared
         * @param c name of the class where the field is declared
         */
        Field(String n, String p, String c, Type t) {
            super(p, c, t);
            name = n.intern();
        }

        @Override
        public boolean equals(Object o) {
            if (super.equals(o) && o instanceof Field) {
                return name.equals(((Field) o).name);
            } else { return false; }
        }

        @Override
        public int hashCode() {
            return 3977 * (inPackage + inClass).hashCode()
                    + 13 * type.hashCode()
                    + name.hashCode();
        }

        @Override
        public String qualifiedName() {
            return (inPackage == "" ? "" : inPackage + ".") + inClass + "#" + name;
        }
    }

    public static final class Parameter extends SpecificationEntity {

        public final String methodName;
        public final String[] paramTypes;
        public final int position;

        /**
         * Creates a new specification element for a method parameter.
         * @param pos the index within the sequence of parameters
         * @param m name of the method with parameter types in parentheses
         * @param p package name of the class where the method is declared
         * @param c name of the class where the method is declared
         */
        Parameter(int pos, String m, String p, String c, Type t) {
            super(p, c, t);
            final int i = m.indexOf('(');
            methodName = m.substring(0, i).intern();
            paramTypes = m.substring(i + 1, m.lastIndexOf(')')).split(",");
            position = pos;
        }

        /**
         * Creates a new specification element for a method parameter.
         * @param pos the index within the sequence of parameters
         * @param m name of the method
         * @param pt names of the parameter types of the method
         * @param p package name of the class where the method is declared
         * @param c name of the class where the method is declared
         */
        Parameter(int pos, String m, String[] pt, String p, String c, Type t) {
            super(p, c, t);
            position = pos;
            methodName = m;
            paramTypes = pt;
        }

        @Override
        public boolean equals(Object o) {
            if (super.equals(o) && o instanceof Parameter) {
                return (methodName.equals(((Parameter) o).methodName)
                        && Arrays.equals(((Parameter) o).paramTypes, paramTypes)
                        && position == ((Parameter) o).position);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return 3661 * (inPackage + inClass).hashCode()
                    + 37 * (methodName.hashCode()
                    + 13 * type.hashCode()
                    + Arrays.hashCode(paramTypes))
                    + position;
        }

        @Override
        public String qualifiedName() {
            final StringBuffer sb = new StringBuffer();
            if (!"".equals(inPackage))
                sb.append(inPackage + ".");
            sb.append(inClass + "#" + methodName + "(");
            int i = 1;
            for (final String p : paramTypes) {
                if (i++ == position) {
                    sb.append(position + ":");
                }
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length()-1);
            sb.append(')');
            return sb.toString();
        }
    }

    public static final class ReturnValue extends SpecificationEntity {

        public final String methodName;
        public final String[] paramTypes;

        /**
         * Creates a new specification element for a method return.
         * @param m name of the method with parameter types in parentheses
         * @param pt names of the parameter types of the method
         * @param p package name of the class where the method is declared
         * @param c name of the class where the method is declared
         */
        ReturnValue(String m, String p, String c, Type t) {
            super(p, c, t);
            final int i = m.indexOf('(');
            methodName = m.substring(0, i).intern();
            paramTypes = m.substring(i + 1, m.lastIndexOf(')')).split(",");
        }

        /**
         * Creates a new specification element for a method return.
         * @param m name of the method
         * @param pt names of the parameter types of the method
         * @param p package name of the class where the method is declared
         * @param c name of the class where the method is declared
         */
        ReturnValue(String m, String[] pt, String p, String c, Type t) {
            super(p, c, t);
            methodName = m;
            paramTypes = pt;
        }

        @Override
        public boolean equals(Object o) {
            if (super.equals(o) && o instanceof ReturnValue) {
                return (methodName.equals(((ReturnValue) o).methodName)
                        && Arrays.equals(paramTypes, ((ReturnValue) o).paramTypes));
            } else { return false; }
        }

        @Override
        public int hashCode() {
            return 3721 * (inPackage + inClass).hashCode()
                    + 79 * methodName.hashCode()
                    + 13 * type.hashCode()
                    + Arrays.hashCode(paramTypes);
        }

        @Override
        public String qualifiedName() {
            final StringBuffer sb = new StringBuffer();
            if (!"".equals(inPackage))
                sb.append(inPackage + ".");
            sb.append(inClass + "#" + methodName + "(");
            for (final String p : paramTypes) {
                sb.append(p);
                sb.append(',');
            }
            sb.deleteCharAt(sb.length()-1);
            sb.append(')');
            return sb.toString();
        }
    }

    public final String inPackage;

    public final String inClass;

    public final Type type;

    private SpecificationEntity(String p, String c, Type t) {
        inPackage = (p == null) ? "" : p.intern();
        inClass = c.intern();
        type = t;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof SpecificationEntity) {
            return (inPackage.equals(((SpecificationEntity) o).inPackage)
                    && inClass.equals(((SpecificationEntity) o).inClass)
                    && (type == ((SpecificationEntity) o).type));
        } else { return false; }
    }

    // //////////////////////////////////////////////////
    // implementations
    // //////////////////////////////////////////////////

    @Override
    public abstract int hashCode();

    public abstract String qualifiedName();

    @Override
    public String toString() {
        return qualifiedName();
    }
}