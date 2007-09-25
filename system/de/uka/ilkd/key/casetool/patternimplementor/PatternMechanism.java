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

import java.io.File;
import java.util.ArrayList;
import java.util.Observable;
import java.util.StringTokenizer;

import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

public class PatternMechanism extends Observable implements
        TreeSelectionListener {

    AbstractPatternImplementor pattern;

    Class[] patterns;

    Class currentClass;

    private boolean isCancelled = false;

    public PatternMechanism() {
        patterns = findAllPatterns();

        try {
            setPattern(patterns[0]);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public void valueChanged(TreeSelectionEvent e) {
        Object source = e.getPath().getLastPathComponent();

        //System.out.println("valueChanged " + e.getPath());
        if (source instanceof PMTreeNode) {
            this.setPattern(((PMTreeNode) source).getPattern());
        } else {
            //System.out.println(source);
        }
    }

    public Class[] getPatterns() {
        return patterns;
    }

    public boolean setPattern(Class patternClass) {
        try {
            setPattern((AbstractPatternImplementor) patternClass.newInstance());

            return true;
        } catch (Exception e) {
            System.err.println("Error when dealing with : "
                    + patternClass.getName());
            e.printStackTrace();
        }

        return false;
    }

    public AbstractPatternImplementor getPattern() {
        return pattern;
    }

    public void setPattern(AbstractPatternImplementor pattern) {
        //System.out.println("setPattern to " + pattern.getName());

        if (!pattern.equals(this.pattern)) {
            this.pattern = pattern;
            this.setChanged();
            this.notifyObservers(this);
        }
    }

    public void cancel() {
	isCancelled = true;
    }

    public SourceCode getImplementation() {
        //if(pattern != null) {
	if (!isCancelled) {
	    return pattern.getImplementation();
	} else {
	    return null;
	}

        //}
        //else
        //    return null;
    }

    public PIParameterGroup getParameters() {
        return pattern.getParameters();
    }

    public String getUIName() {
        return pattern.getName();
    }

    private static Class[] findAllPatterns() {
        ArrayList the_patterns = new ArrayList();

        String packageUrl = AbstractPatternImplementor.class.getPackage()
                .toString();
        packageUrl = packageUrl.substring(packageUrl.indexOf(" ") + 1);

        byte[] packageUrlasArray = packageUrl.getBytes();

        for (int i = 0; i < packageUrlasArray.length; i++) {
            if (packageUrlasArray[i] == '.') {
                packageUrlasArray[i] = (byte) File.separatorChar;
            }
        }

        String packagePath = new String(packageUrlasArray);
        packagePath = File.separatorChar + packagePath + File.separatorChar
                + "patterns" + File.separatorChar;
        //System.out.println(packagePath + "\t" + packageUrl);

        String classPath = System.getProperty("java.class.path", ".");

        StringTokenizer cp = new StringTokenizer(classPath, File.pathSeparator);

        while (cp.hasMoreTokens()) {
            String cPath = cp.nextToken();

            //System.out.println("Full path = " + cPath + "\t" + packagePath);

            //URL url =
            // AbstractPatternImplementor.class.getResource(cPath+packagePath);
            //System.out.println("URL = " + url + "\t");
            //File directory = new File(url.getFile());
            File directory = new File(cPath + packagePath);

            if (directory.exists()) {
                String[] files = directory.list();

                //Class[] patterns = new Class[files.length];
                for (int i = 0; i < files.length; i++) {
                    //System.out.println("file : " + files[i]);

                    if (files[i].endsWith(".class")) {
                        try {
                            String tmp = files[i].substring(0, files[i]
                                    .length() - 6);
                            tmp = packageUrl + ".patterns." + tmp;
                            //System.err.println(tmp);

                            Class c = Class.forName(tmp);
                            Class[] interfaces = c.getInterfaces();

                            for (int j = 0; j < interfaces.length; j++) {
                                if (interfaces[j]
                                        .equals(AbstractPatternImplementor.class /* .getName() */)) {
                                    the_patterns.add(c);
                                    //System.err.print(c.getName());
                                    //System.err
				    //      .println("\t"
				    //              + interfaces[j]
				    //                      .equals(AbstractPatternImplementor.class));
                                } else {
                                    //System.out.println(""+c.getName());
                                }
                            }
                        } catch (Exception e) {
                            System.err.println("Error with " + files[i]);
                            e.printStackTrace();
                        }
                    }
                }
            }
        }

        Class[] retval = new Class[the_patterns.size()];

        for (int i = 0; i < the_patterns.size(); i++) {
            retval[i] = ((Class) the_patterns.get(i));
            //System.err.print(retval[i].toString() + "\t");
        }

        //System.err.println("");

        return retval;
    }   
}
