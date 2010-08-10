// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

public class SourceCode extends java.util.Vector {

    public String toString() {
        String retval = new String();

        retval = toText(true);
        retval = retval + "-----------------\nNumber of classes : "
                + nofClasses() + "\n";

        /*
         * if(nofClasses() > 4) { retval = retval + getClass(0); }
         */
        return retval.trim();
    }

    public String getClassName() {
        for (int i = 0; i < size(); i++) {
            if (elementAt(i) instanceof ClassDelimiter) { return ((ClassDelimiter) elementAt(i))
                    .getName(); }
        }
        return null;
    }

    public String toText() {
        return toText(false);
    }

    public String toText(boolean includingClassDelimiter) {
        String retval = new String();
        for (int i = 0; i < size(); i++) {
            if (includingClassDelimiter) {
                retval = retval + elementAt(i).toString() + "\n";
            } else {
                if (!(elementAt(i) instanceof ClassDelimiter)) {
                    retval = retval + elementAt(i).toString() + "\n";
                }
            }

        }
        return retval;
    }

    public void add() {
        add("");
    }

    public boolean add(Object sc) {
        if (sc != null) { return super.add(sc); }

        return false;
    }

    public void add(SourceCode sc) {
        for (int i = 0; i < sc.size(); i++) {
            add(sc.elementAt(i));
        }
    }

    public void beginClass(String name) {
        if (name.indexOf(".java") == -1) {
            add(new ClassDelimiter(name + ".java"));
        } else {
            add(new ClassDelimiter(name));
        }
    }

    /*
     * class Context { private String context; Context(String context){
     * this.context = context; } public String toString() { return "// context :
     * "+context; } }
     */
    public int nofClasses() {
        int counter = 0;

        //System.out.println(".................................");
        for (int i = 0; i < size(); i++) {
            if (elementAt(i) instanceof ClassDelimiter) {
                counter++;
            }
        }

        return counter;
    }

    /**
     * 
     * @param index -
     *            index of the class to be returned
     * @return the index:th class. The classes are numbered from 0 to
     *         nofClasses-1. If the index given outside the possible range, an
     *         empty SourceCode will be returned.
     */
    public SourceCode getClass(int index) {
        int counter = -1;
        SourceCode retval = new SourceCode();

        //System.out.println(".................................");
        for (int i = 0; i < size(); i++) {
            if (elementAt(i) instanceof ClassDelimiter) {
                counter++;

                if (counter == index) {
                    int j = i + 1;
                    retval.add(elementAt(i));

                    while ((j < size())
                            && !(elementAt(j) instanceof ClassDelimiter)) {
                        retval.add(elementAt(j));
                        j++;
                    }

                    return retval;
                }
            }
        }

        return retval;
    }

    /*
     * public void setContext(String context) { add(new Context(context)); }
     */
    class ClassDelimiter {

        private String name;

        ClassDelimiter(String name) {
            this.name = name;
        }

        public String toString() {
            return "8<--------- " + name + " -----------";
        }

        public String getName() {
            return name;
        }
    }
}
