// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor.patterns;
import de.uka.ilkd.key.casetool.patternimplementor.*;

public class AbstractFactory implements AbstractPatternImplementor {
    private PIParameterGroup abstractFactory;
    private ConstraintMechanism constraintMechanism;

    public PIParameterGroup getParameters() {
        if (abstractFactory == null) {
            createParameters();
        }

        return abstractFactory;
    }

    /*public AbstractFactory()
    {

            createParameters();
    }*/
    protected void createParameters() {
        abstractFactory = new PIParameterGroup("AbstractFactoryPattern",
                "Abstract Factory Pattern");

        PIParameterString af = new PIParameterString("AbstractFactory",
                "Abstract factory", "AbstractFactory");
        PIParameterMultiString ap = new PIParameterMultiString("AbstractProduct",
                "Abstract products", "AbstractProduct");
        PIParameterMultiString cf = new PIParameterMultiString("ConcreteFactory",
                "Concrete factories", "ConcreteFactory1 ConcreteFactory2");
        PIParameterDependent cp = new PIParameterDependent("ConcreteProduct",
                "Concrete products", cf);

        abstractFactory.add(af);
        abstractFactory.add(ap);
        abstractFactory.add(cf);
        abstractFactory.add(cp);
        constraintMechanism = new ConstraintMechanism("AbstractFactory.constraints",
                abstractFactory, this);

        /*System.out.println("abstractFactory {");
        System.out.println(abstractFactory);
        System.out.println("}");*/
    }

    /*public void createAbstractFactoryDialog() {
            JDialog jd = new JDialog();
            jd.setContentPane(new PIParameterGUIGroup(abstractFactory));
            jd.pack();
            jd.setVisible(true);
    }*/
    private SourceCode createConcreteFactory() {
        String af = abstractFactory.get("AbstractFactory").getValue();
        String[] cf = ((PIParameterMultiString) abstractFactory.get(
                "ConcreteFactory")).getValues();
        String[] ap = ((PIParameterMultiString) abstractFactory.get(
                "AbstractProduct")).getValues();
        String[][] cps = ((PIParameterGroup) abstractFactory.get(
                "ConcreteProduct")).getValues();

        SourceCode source = new SourceCode();

        for (int i = 0; i < cf.length; i++) {
            source.beginClass(cf[i]);
            source.add("/**");
            source.add(constraintMechanism.getConstraints(" * ",
                    "ConcreteFactory", cf[i]));
            source.add(" */");
            source.add("public class " + cf[i] + " extends " + af + " {");

            // fulhack?
            for (int j = 0; j < Math.min(ap.length, cps[i].length); j++) {
                source.add("\t/**");
                source.add(constraintMechanism.getConstraints("\t * ",
                        "ConcreteFactory::createProduct",
                        cf[i] + "::" + cps[i][j]));
                source.add("\t */");
                source.add("\tpublic " + ap[j] + " Create" + ap[j] + "() {");
                source.add("\t\treturn new " + cps[i][j] + "();");
                source.add("\t}");
            }

            source.add("}");
        }

        return source;
    }

    private SourceCode createConcreteProducts() {
        String[] ap = ((PIParameterMultiString) abstractFactory.get(
                "AbstractProduct")).getValues();
        String[][] cps = ((PIParameterGroup) abstractFactory.get(
                "ConcreteProduct")).getValues();

        //SourceCode classes = new SourceCode();
        SourceCode source = new SourceCode();

        for (int j = 0; j < cps.length; j++) {
            //Property cp = (Property)concreteProducts.elementAt(j);
            for (int i = 0; i < Math.min(ap.length, cps[j].length); i++) {
                //SourceCode source = new SourceCode();
                source.beginClass(cps[j][i]);
                source.add("/**");
                source.add(constraintMechanism.getConstraints(" * ",
                        "ConcreteProduct", cps[j][i]));
                source.add(" */");

                source.add("public class " + cps[j][i] + " extends " + ap[i] +
                    " {");
                source.add("}");

                //classes.add(source);
            }
        }

        return source; //classes;
    }

    private SourceCode createAbstractProducts() {
        String[] ap = ((PIParameterMultiString) abstractFactory.get(
                "AbstractProduct")).getValues();

        //SourceCode classes = new SourceCode();
        SourceCode source = new SourceCode();

        for (int i = 0; i < ap.length; i++) {
            //SourceCode source = new SourceCode();
            source.beginClass(ap[i]);
            source.add("/**");
            source.add(constraintMechanism.getConstraints(" * ",
                    "AbstractProduct", ap[i]));
            source.add(" */");
            source.add("public class " + ap[i] + " {");
            source.add("}");

            //classes.add(source);
        }

        return source;

        //return classes;
    }

    private SourceCode createAbstractFactory() {
        String af = abstractFactory.get("AbstractFactory").getValue();
        String[] ap = ((PIParameterMultiString) abstractFactory.get(
                "AbstractProduct")).getValues();

        SourceCode source = new SourceCode();
        source.beginClass(af);
        source.add("/**");
        source.add(constraintMechanism.getConstraints(" * ", "AbstractFactory",
                af));
        source.add(" */");
        source.add("public abstract class " + af + " {");

        for (int i = 0; i < ap.length; i++) {
            String tmp = ap[i];
            source.add("\t/**");
            source.add(constraintMechanism.getConstraints("\t * ",
                    "AbstractFactory::createProduct", af + "::" + ap[i]));
            source.add("\t */");
            source.add("\tpublic abstract " + ap[i] + " Create" + tmp + "();");
        }

        source.add("}");

        return source;
    }

    public SourceCode getImplementation() {
        if (abstractFactory == null) {
            System.err.println(
                "ERROR - AbstractFactory,getImplementor : abstractFactory == null");

            return null;
        }

        SourceCode code = new SourceCode();
        code.add(createConcreteFactory());
        code.add(createConcreteProducts());
        code.add(createAbstractProducts());
        code.add(createAbstractFactory());

        return code;
    }

    public String getName() {
        return "Creational Patterns:Abstract Factory";
    }
}
