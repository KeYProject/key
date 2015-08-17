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

/**
 * Program elements which may be named as sources or sinks in RIFL/Java.
 * Currently fields, method parameters, and method return values can be
 * named both sources and sinks.
 * 
 * @author bruns
 */
public abstract class SpecificationEntity {

    public static final class Field extends SpecificationEntity {

        public final String name;

        /**
         * Creates a new specification element for a field.
         * @param n name of the field
         * @param p package name of the class where the field is declared
         * @param c name of the class where the field is declared
         */
        Field(String n, String p, String c) {
            super(p, c);
            name = n.intern();
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof Field) {
                return (inPackage.equals(((Field) o).inPackage)
                        && inClass.equals(((Field) o).inClass) && name
                            .equals(((Field) o).name));
            } else
                return false;
        }

        @Override
        public int hashCode() {
            return 3977 * (inPackage + inClass).hashCode() + name.hashCode();
        }

        @Override
        public String qualifiedName() {
            return (inPackage == "" ? "" : inPackage + ".") + inClass + "#"
                    + name;
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
        Parameter(int pos, String m, String p, String c) {
            super(p, c);
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
        Parameter(int pos, String m, String[] pt, String p, String c) {
            super(p, c);
            position = pos;
            methodName = m;
            paramTypes = pt;
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof Parameter) {
                return (inPackage.equals(((Parameter) o).inPackage)
                        && inClass.equals(((Parameter) o).inClass)
                        && methodName.equals(((Parameter) o).methodName)
                        && paramTypes.equals(((Parameter) o).paramTypes) && position == ((Parameter) o).position);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return 3661 * (inPackage + inClass).hashCode() + 37
                    * (methodName.hashCode() + paramTypes.hashCode())
                    + position;
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
        ReturnValue(String m, String p, String c) {
            super(p, c);
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
        ReturnValue(String m, String[] pt, String p, String c) {
            super(p, c);
            methodName = m;
            paramTypes = pt;
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof ReturnValue) {
                return (inPackage.equals(((ReturnValue) o).inPackage)
                        && inClass.equals(((ReturnValue) o).inClass)
                        && methodName.equals(((ReturnValue) o).methodName) && paramTypes
                            .equals(((ReturnValue) o).paramTypes));
            } else
                return false;
        }

        @Override
        public int hashCode() {
            return 3721 * (inPackage + inClass).hashCode() + 79
                    * methodName.hashCode() + paramTypes.hashCode();
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

    private SpecificationEntity(String p, String c) {
        inPackage = (p == null) ? "" : p.intern();
        inClass = c.intern();
    }

    @Override
    public abstract boolean equals(Object o);

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
