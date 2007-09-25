// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor.patterns;
import de.uka.ilkd.key.casetool.patternimplementor.*;

public class Singleton implements AbstractPatternImplementor {
    private PIParameterGroup singleton;
    private ConstraintMechanism constraintMechanism;

    public String getName() {
        return "Creational Patterns:Singleton";
    }

    public PIParameterGroup getParameters() {
        if (singleton == null) {
            createParameters();
        }

        return singleton;
    }

    protected void createParameters() {
        singleton = new PIParameterGroup("SingletonPattern", "Singleton Pattern");

        PIParameterString s_class = new PIParameterString("Singleton_class",
                "Singleton", "Singleton");
        PIParameterString s_instance = new PIParameterString("unique_instance_attribute",
                "Unique instance attribute", "instance");
        PIParameterString s_getInstance = new PIParameterString("s_getInstance",
                "Instance method", "getInstance");

        singleton.add(s_class);
        singleton.add(s_instance);
        singleton.add(s_getInstance);
        constraintMechanism = new ConstraintMechanism("Singleton.constraints",
                singleton, this);

        /*System.out.println("Singleton {");
        System.out.println(singleton);
        System.out.println("}");*/
    }

    public SourceCode getImplementation() {
        String s_class = singleton.get("Singleton_class").getValue();
        String s_instance = singleton.get("unique_instance_attribute").getValue();
        String s_getInstance = singleton.get("s_getInstance").getValue();

        SourceCode sc = new SourceCode();
        sc.beginClass(s_class);
        sc.add("/**");
        sc.add(constraintMechanism.getConstraints(" * ", "Singleton", s_class));
        sc.add(" */");
        sc.add("class " + s_class + "{");
	sc.add("\t/**");
	sc.add("\t * @supplierRole " + s_instance);
	sc.add("\t */");
        sc.add("\tprivate static " + s_class + " " + s_instance + ";");
        sc.add("\t/*");
        sc.add(constraintMechanism.getConstraints("\t * ", "Singleton::create",
                s_class + "::" + s_class));
        sc.add("\t */");
        sc.add("\tprotected " + s_class + "() {}");
        sc.add("\t/*");
        sc.add(constraintMechanism.getConstraints("\t * ",
                "Singleton::getInstance", s_getInstance));
        sc.add("\t */");
        sc.add("\tpublic static " + s_class + " " + s_getInstance + "() {");
        sc.add("\t\tif(" + s_instance + " == null) {");
        sc.add("\t\t\t" + s_instance + " = new " + s_class + "();");
        sc.add("\t\t}");
        sc.add("\t\treturn " + s_instance + ";");
        sc.add("\t}");
        sc.add("}");

        return sc;
    }
}
