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

public class Composite implements AbstractPatternImplementor {
    private PIParameterGroup composite;
    private ConstraintMechanism constraintMechanism;

    public PIParameterGroup getParameters() {
        if (composite == null) {
            createParameters();
        }

        return composite;
    }

    /*public AbstractFactory()
    {

            createParameters();
    }*/
    protected void createParameters() {
        composite = new PIParameterGroup("Composite",
                "Composite");

	//param1 = internal name, param2 = name, param3 = value (i.e.what gets 
	//returned from PIParameter::getValue())
	PIParameterString c_class = new PIParameterString("Composite_class",
                "Composite", "Composite");
	PIParameterString children_attr = new PIParameterString("children_attribute",
                "Children attribute", "children");

        PIParameterString component = new PIParameterString("Component",
                "Component", "Component");
        PIParameterString leaf = new PIParameterMultiString("Leaf",
                "Leaf", "Leaf");

	composite.add(component);
        composite.add(leaf);
        composite.add(c_class);
        composite.add(children_attr);
        constraintMechanism = new ConstraintMechanism("Composite.constraints",
                composite, this);

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
    private SourceCode createComponent() {
        String comp = composite.get("Component").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(comp);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "Component", comp));
	source.add(" */");
	source.add("public class " + comp + " {");
	source.add("\tpublic void add(" + comp + " c) {}");
	source.add("}");

        return source;
    }

    private SourceCode createComposite() {
	String component = composite.get("Component").getValue();
        String comp = composite.get("Composite_class").getValue();
	String children = composite.get("children_attribute").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(comp);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "Composite", comp));
	source.add(" */");
	source.add("public class " + comp + " extends " + component + " {");
	source.add("\tpublic void add(" + component + " c) {}");
	source.add("\t/**");
	source.add("\t * @supplierCardinality 1..*");
	source.add("\t * @supplierRole " + children);
	source.add("\t * @supplierQualifier {ordered}");
	source.add("\t */");
	source.add("\tprivate " + component + " lnk" + component + ";");
	source.add("}");

        return source; //classes;
    }

    private SourceCode createLeaf() {
	String component = composite.get("Component").getValue();
        String leaf = composite.get("Leaf").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(leaf);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "Leaf", leaf));
	source.add(" */");
	source.add("public class " + leaf + " extends " + component + " {");
	source.add("\tpublic void add(" + component + " c) {}");
	source.add("}");

        return source;
    }

    public SourceCode getImplementation() {
        if (composite == null) {
            System.err.println(
                "ERROR - AbstractFactory,getImplementor : abstractFactory == null");

            return null;
        }

        SourceCode code = new SourceCode();
        code.add(createComponent());
        code.add(createComposite());
        code.add(createLeaf());

        return code;
    }

    public String getName() {
        return "Creational Patterns:Composite";
    }
}
