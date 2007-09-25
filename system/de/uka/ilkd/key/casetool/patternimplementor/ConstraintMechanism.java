// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.Stack;
import java.util.StringTokenizer;
import java.util.Vector;

public class ConstraintMechanism {

    private static final String POST = "@postconditions ";

    private static final String PRE = "@preconditions ";

    private static final String INV = "@invariants ";

    private static final String DEF = "@definitions ";

    //	private static final String EPOST= "@extended_postcondition ";
    //	private static final String SINV = "@static_invariant ";
    private static final String KeyBOOLEAN = "[Boolean]";

    private static final String KeyVOID = "[Void]";

    private static final String KeySTRING = "[String]";

    private static final String KeyMSTRING = "[MultiString]";

    private static final String KeyGROUP = "[Group]";

    private static final String KeyENDGROUP = "[EndGroup]";

    private static final String KeyDEPEND = "[Dependent]";

    private static final String KeyCONTEXT = "[Context]";

    private static final String KeyPOST = "[PostCondition]";

    private static final String KeyPRE = "[PreCondition]";

    private static final String KeyINV = "[Invariant]";

    private static final String KeyDEF = "[Definition]";

    //String filename;
    PIParameterGroup parameterGroup;

    Vector constraints;

    /*
     * public ConstraintMechanism(PIParameterGroup parameterGroup) { }
     */
    public ConstraintMechanism(String filename,
            PIParameterGroup parameterGroup, AbstractPatternImplementor api) {
        //this(parameterGroup);
        this.parameterGroup = parameterGroup;
        this.constraints = new Vector();

        String packagePath = api.getClass().getPackage().toString();
        packagePath = packagePath.substring(packagePath.indexOf(" ") + 1);

        byte[] pathArray = packagePath.getBytes();

        for (int i = 0; i < pathArray.length; i++) {
            if (pathArray[i] == '.') {
                pathArray[i] = (byte) File.separatorChar;
            }
        }

        parseFile(new String(pathArray) + File.separatorChar + filename);
    }

    private void parseFile(String filename) {
        //System.err.println("Trying to parse " + filename);

        try {
            BufferedReader infile = null;

            String classPath = System.getProperty("java.class.path", ".");

            StringTokenizer cp = new StringTokenizer(classPath,
                    File.pathSeparator);

            while (cp.hasMoreTokens()) {
                String cPath = cp.nextToken();
                //System.err.println("looking in " + cPath + File.separatorChar
		//      + filename);
                File f = new File(cPath + File.separatorChar + filename);
                if (f.exists()) {
                    FileReader fr = new FileReader(cPath + File.separatorChar
                            + filename);
                    infile = new BufferedReader(fr);
                    break;
                }
            }
            if (infile == null) { return; }

            String indata;
            Stack groupStack = new Stack();
            int linenumber = 0;

            String currentContext = null;

            groupStack.push(new PIParameterGroup("constraintGroup",
                    "Constraints"));

            while ((indata = infile.readLine()) != null) {
                linenumber++;

                // remove comments
                int index = indata.indexOf("//");

                if (index != -1) {
                    indata = indata.substring(0,
                            ((index - 1) > 0) ? (index - 1) : 0);
                }

                indata = indata.trim();

                try {
                    if (indata.indexOf(KeyBOOLEAN) != -1) {
                        parseBoolean(indata, groupStack);
                    } else if (indata.indexOf(KeyDEPEND) != -1) {
                        // [Dependent]
                        //System.out.print("DEPEND");
                    } else if (indata.indexOf(KeyENDGROUP) != -1) {
                        // [EndGroup]
                        groupStack.pop();
                    } else if (indata.indexOf(KeyGROUP) != -1) {
                        parseGroupBegin(indata, groupStack);
                    } else if (indata.indexOf(KeyMSTRING) != -1) {
                        parseMultiString(indata, groupStack);
                    } else if (indata.indexOf(KeySTRING) != -1) {
                        parseString(indata, groupStack);
                    } else if (indata.indexOf(KeyVOID) != -1) {
                        parseVoid(indata, groupStack);
                    } else if (indata.indexOf(KeyCONTEXT) != -1) {
                        currentContext = parseContext(indata);
                    } else if (indata.indexOf(KeyPOST) != -1) {
                        parseConstraint(indata, currentContext, POST);
                    } else if (indata.indexOf(KeyPRE) != -1) {
                        parseConstraint(indata, currentContext, PRE);
                    } else if (indata.indexOf(KeyINV) != -1) {
                        parseConstraint(indata, currentContext, INV);
                    } else if (indata.indexOf(KeyDEF) != -1) {
                        parseConstraint(indata, currentContext, DEF);
                    } else {
                    }
                } catch (Exception e) {
                    // ignore syntax error for now
                    System.err.println("Syntax error in " + filename
                            + " at line " + linenumber);
                }
            }

            if (groupStack.size() == 1) {
                //parameterGroup = (PIParameterGroup)groupStack.pop();
                //System.out.println("Doesn't assign parameterGroup");
                //return (PIParameterGroup)groupStack.pop();
                parameterGroup.add((PIParameterGroup) groupStack.pop());
            } else {
                System.err.println("Unbalanced [Group]-[EndGroup] in "
                        + filename);
            }
        } catch (Exception e) {
            System.err.println("Couldn't open file : " + filename);
            e.printStackTrace();
        }

        //System.out.println("ConstraintMechanism.parseFile - returns null");
        //return null;
    }

    private void parseConstraint(String indata, String currentContext,
            String type) {
        // [PostCondition] ocl-expression
        // [PreCondition] ocl-expression
        // [Invariant] ocl-expression
        // [Definition] ocl-expression
        if (currentContext == null) {
            System.err.println("Skipping " + indata + " since context unknown");
        } else {
            int a = indata.indexOf(']');
            String constraint = indata.substring(a + 1).trim();

            //System.out.println(POST+ " " + postcond);          
            Constraint c = new Constraint(currentContext, constraint, type);            
            constraints.add(c);
        }
    }

    private String parseContext(String indata) {
        String currentContext;

        // [Context] context::context
        int a = indata.indexOf(']');

        currentContext = new String(indata.substring(a + 1).trim());

        /*
         * a = indata.indexOf('"'); int b = indata.indexOf('"',a+1);
         * currentContext = currentContext.substring(a+1,b);
         */
        return currentContext;
    }

    private void parseVoid(String indata, Stack groupStack) {
        // [Void] "name"
        int a = indata.indexOf('"');
        int b = indata.indexOf('"', a + 1);
        String name = indata.substring(a + 1, b);
        ((PIParameterGroup) groupStack.peek()).add(new PIParameterVoid(name));
    }

    private void parseString(String indata, Stack groupStack) {
        // [String] "internalName", "name", "value"
        String internalName;
        String name;
        String value;

        int a = indata.indexOf('"');
        int b = indata.indexOf('"', a + 1);
        internalName = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        name = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        value = indata.substring(a + 1, b);

        //System.out.print("STRING ->"+internalName+","+name+","+value+"<-");
        ((PIParameterGroup) groupStack.peek()).add(new PIParameterString(
                internalName, name, value));
    }

    private void parseMultiString(String indata, Stack groupStack) {
        // [MultiString] "internalName", "name", "value"
        String internalName;
        String name;
        String value;

        int a = indata.indexOf('"');
        int b = indata.indexOf('"', a + 1);
        internalName = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        name = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        value = indata.substring(a + 1, b);

        //System.out.print("MSTR ->"+internalName+","+name+","+value+"<-");
        ((PIParameterGroup) groupStack.peek()).add(new PIParameterMultiString(
                internalName, name, value));
    }

    private void parseGroupBegin(String indata, Stack groupStack) {
        // [Group] "internalName", "name"
        String internalName;
        String name;

        int a = indata.indexOf('"');
        int b = indata.indexOf('"', a + 1);
        internalName = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        name = indata.substring(a + 1, b);

        //System.out.print("GROUP ->"+internalName+","+name+"<-");
        PIParameterGroup newgrp = new PIParameterGroup(internalName, name);

        ((PIParameterGroup) groupStack.peek()).add(newgrp);
        groupStack.push(newgrp);
    }

    private void parseBoolean(String indata, Stack groupStack) {
        // [Boolean] "internalName", "name", "value"
        String internalName;
        String name;
        String value;

        int a = indata.indexOf('"');
        int b = indata.indexOf('"', a + 1);
        internalName = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        name = indata.substring(a + 1, b);

        a = indata.indexOf('"', b + 1);
        b = indata.indexOf('"', a + 1);
        value = indata.substring(a + 1, b);

        //System.out.print("BOOL ->"+internalName+","+name+","+value+"<-");
        ((PIParameterGroup) groupStack.peek()).add(new PIParameterBoolean(
                internalName, name, value));
    }

    public PIParameterGroup getPIParameterGroup() {
        return parameterGroup; //parameterGroup;
    }

    public String getConstraints(String prefix, String context,
            String realContext) {
        Vector postconditions = new Vector();
        Vector preconditions  = new Vector();
        Vector invariants     = new Vector();
        Vector definitions    = new Vector();

        //Vector staticinv = new Vector();
        //Vector extendedpost = new Vector();
        String retval = new String();

        for (int i = 0; i < constraints.size(); i++) {
            //System.out.println("...."+((Constraint)constraints.elementAt(i)));
            if (((Constraint) constraints.elementAt(i)).getContext().equals(
                    context)) {
                String constraint = "("
                        + ((Constraint) constraints.elementAt(i))
                                .getConstraint(context, parameterGroup) + ")";
                String type = ((Constraint) constraints.elementAt(i)).getType();

                if (type.equals(POST)) {
                    postconditions.add(constraint);
                } else if (type.equals(PRE)) {
                    preconditions.add(constraint);
                } else if (type.equals(INV)) {
                    invariants.add(constraint);
                } else if (type.equals(DEF)) {
                    definitions.add(constraint);
                } else {
                    System.err
                            .println("ConstraintMechanism.getConstraints - unknown Constraint type : \""
                                    + type + "\"");
                }
            }
        }

        retval = retval + constraintConjunction(prefix + PRE, preconditions);
        retval = retval + constraintConjunction(prefix + INV, invariants);
        retval = retval + constraintConjunction(prefix + DEF, definitions);
        retval = retval + constraintConjunction(prefix + POST, postconditions);

        if (retval.equals("")) {
            retval = null;
        }

        return retval;
    }

    private String constraintConjunction(String prefix, Vector constraints) {
        String retval = new String();

        for (int i = 0; i < constraints.size(); i++) {
	    if (i == 0) {
		retval = retval + prefix + constraints.elementAt(i);
            } else {
                retval = retval + " and " + constraints.elementAt(i);
	    }
        }

        return retval;
    }

    class Constraint {

        private static final String BEGIN = "<:";

        private static final String END = ":>";

        private String context;

        private String constraint;

        private String type;

        Constraint(String context, String constraint, String type) {
            this.type = type;
            this.context = context;
            this.constraint = constraint;
        }

        public String getContext() {
            return context;
        }

        /*
         * alternativ psuedokod - varken testad eller anv�nd :| input = 1234
         * <:5678:>90abc <:def:>ghi ^ ^ ^ ^ ^ p0 p1 p2 p3 p4
         * 
         * String result = new String(); boolean textmode = input.indexOf(" <:") ==
         * p[0]; for(int i = 0; i < p.size()-1 ; i++) { if(textmode) { result =
         * result + input.substring(p[i], p[i+1]); } else // replacemode {
         * String replaceval = getReplaceval(input.substring(p[i],p[i+1]);
         * result = result + replaceval; } textmode != textmode; }
         *  
         */
        public String getConstraint(String context, PIParameterGroup pipg) {
            String instantiatedConstraint = new String();

            if (context.equals(this.context)) {
                instantiatedConstraint = constraint;

                Vector placeholders = searchPlaceholders(instantiatedConstraint);
                int size = placeholders.size();

                for (int i = 0; i < size; i++) {
                    placeholders = searchPlaceholders(instantiatedConstraint);

                    int a = ((int[]) placeholders.elementAt(0))[0];
                    int b = ((int[]) placeholders.elementAt(0))[1];
                    String pre = instantiatedConstraint.substring(0, a
                            - BEGIN.length());
                    String tmp = instantiatedConstraint.substring(a, b);
                    String post = instantiatedConstraint.substring(b
                            + END.length(), instantiatedConstraint.length());

                    //System.out.println("...'"+pre+"'"+tmp+"'"+post+"'...");
                    //System.out.println("Trying to get things from
                    // "+pipg.getInternalName());
                    PIParameter value = pipg.get(tmp);

                    if (value != null) {
                        instantiatedConstraint = pre + value.getValue() + post;
                    }
                }
            } else {
                System.out.println("wrong context" + this.context + " != "
                        + context);
            }

            return instantiatedConstraint;
        }

        public Vector searchPlaceholders(String constraint) {
            Vector placeholders = new Vector();

            int a = 0;
            int b = 0;
            int pointer = 0;

            while (true) {
                a = constraint.indexOf(BEGIN, pointer);
                b = constraint.indexOf(END, a + 1);
                pointer = b + 1;

                if ((a == -1) || (b == -1)) {
                    break;
                } else {
                    a = a + BEGIN.length();

                    //b = b;
                    //System.out.println("Start " + a + " \tEnd " +b);
                    int[] tmp = new int[2];
                    tmp[0] = a;
                    tmp[1] = b;
                    placeholders.add(tmp);
                }
            }

            return placeholders;
        }

        public String toString() {
            return "context " + context + "\n" + type + ": " + constraint;
        }

        public String getType() {
            return type;
        }
    }
}
