// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor.patterns;
import de.uka.ilkd.key.casetool.patternimplementor.*;

public class Observer implements AbstractPatternImplementor {
    private PIParameterGroup observer;
    private ConstraintMechanism constraintMechanism;

    public PIParameterGroup getParameters() {
        if (observer == null) {
            createParameters();
        }

        return observer;
    }

    protected void createParameters() {
        observer = new PIParameterGroup("Observer",
                "Observer");

	PIParameterString observer_class = new PIParameterString("Observer_class",
                "Observer", "AbstractObserver");
	//PIParameterString concreteobserver_class = new PIParameterString("ConcreteObserver_class",
        //        "ConcreteObserver", "ConcreteObserver");
	PIParameterString subject_class = new PIParameterString("Subject_class",
                "Subject", "Subject");
	PIParameterString concretesubject_class = new PIParameterString("ConcreteSubject_class",
                "ConcreteSubject", "ConcreteSubject");
	PIParameterString observers_ass = new PIParameterString("observers_ass",
                "Observers Association", "observers");
	PIParameterString subject_ass = new PIParameterString("subject_ass",
                "Subject Association", "subject");

	PIParameterMultiString concreteobservers = new PIParameterMultiString("ConcreteObserver_class",
                "Concrete observers", "ConcreteObserver1 ConcreteObserver2");
        //PIParameterDependent cp = new PIParameterDependent("ConcreteProduct",
	//       "Concrete products", cf);

	observer.add(observer_class);
        //observer.add(concreteobserver_class);
	observer.add(concreteobservers);
        observer.add(subject_class);
        observer.add(concretesubject_class);
	observer.add(observers_ass);
	observer.add(subject_ass);
        constraintMechanism = new ConstraintMechanism("Observer.constraints",
                observer, this);
    }

    private SourceCode createObserver() {
        String observerName = observer.get("Observer_class").getValue();
	String subjectAssName = observer.get("subject_ass").getValue();
	String concSubjName = observer.get("ConcreteSubject_class").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(observerName);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "Observer", observerName));
	source.add(" */");
	source.add("public class " + observerName + " {");
	source.add("\tpublic void update() {}");
	source.add("\t/**");
	source.add("\t * @supplierCardinality 0..1");
	source.add("\t * @supplierRole " + subjectAssName);
	source.add("\t */");
	source.add("\tprivate " + concSubjName + " lnk" + concSubjName + ";");
	source.add("}");

        return source;
    }

    private SourceCode createConcreteObservers() {
	String[] concObsName 
	    = ((PIParameterMultiString) observer.get("ConcreteObserver_class")).getValues();
	String observerName = observer.get("Observer_class").getValue();
	String subjectAssName = observer.get("subject_ass").getValue();
	String concSubjName = observer.get("ConcreteSubject_class").getValue();

        SourceCode source = new SourceCode();

	for (int i=0; i<concObsName.length; i++) {
	    source.beginClass(concObsName[i]);
	    source.add("/**");
	    source.add(constraintMechanism.getConstraints(" * ",
							  "ConcreteObserver", concObsName[i]));
	    source.add(" */");
	    source.add("public class " + concObsName[i] + " extends " + observerName + " {");
	    source.add("\tpublic void update() {}");
	    source.add("\t/**");
	    source.add("\t * @supplierCardinality 0..1");
	    source.add("\t * @supplierRole " + subjectAssName);
	    source.add("\t */");
	    source.add("\tprivate " + concSubjName + " lnk" + concSubjName + ";");
	    source.add("}");
	}

        return source; //classes;
    }

    private SourceCode createConcreteObserver() {
	String concObsName = observer.get("ConcreteObserver_class").getValue();
	String observerName = observer.get("Observer_class").getValue();
	String subjectAssName = observer.get("subject_ass").getValue();
	String concSubjName = observer.get("ConcreteSubject_class").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(concObsName);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "ConcreteObserver", concObsName));
	source.add(" */");
	source.add("public class " + concObsName + " extends " + observerName + " {");
	source.add("\tpublic void update() {}");
	source.add("\t/**");
	source.add("\t * @supplierCardinality 0..1");
	source.add("\t * @supplierRole " + subjectAssName);
	source.add("\t */");
	source.add("\tprivate " + concSubjName + " lnk" + concSubjName + ";");
	source.add("}");

        return source; //classes;
    }

    private SourceCode createSubject() {
	String subjectName = observer.get("Subject_class").getValue();
	String observerName = observer.get("Observer_class").getValue();
	String observersAssName = observer.get("observers_ass").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(subjectName);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "Subject", subjectName));
	source.add(" */");
	source.add("public class " + subjectName + " {");
	source.add("\tpublic void attach(" + observerName + " o) {}");
	source.add("\tpublic void detach(" + observerName + " o) {}");
	source.add("\tpublic void notify() {}");
	source.add("\t/**");
	source.add("\t * @supplierCardinality 0..*");
	source.add("\t * @supplierRole " + observersAssName);
	source.add("\t */");
	source.add("\tprivate " + observerName + " lnk" + observerName + ";");
	source.add("}");

        return source; //classes;
    }

    private SourceCode createConcreteSubject() {
        String concSubjName = observer.get("ConcreteSubject_class").getValue();
	String subjectName = observer.get("Subject_class").getValue();

        SourceCode source = new SourceCode();

	source.beginClass(concSubjName);
	source.add("/**");
	source.add(constraintMechanism.getConstraints(" * ",
                    "ConcreteSubject", concSubjName));
	source.add(" */");
	source.add("public class " + concSubjName + " extends " + subjectName + " {");
	source.add("\tpublic Object getState() {}");
	source.add("\tpublic void setState(Object state) {}");
	source.add("}");

        return source;
    }

    public SourceCode getImplementation() {
        if (observer == null) {
            System.err.println(
                "ERROR - Observer.getImplementation : observer == null");

            return null;
        }

        SourceCode code = new SourceCode();
        code.add(createObserver());
        code.add(createSubject());
	code.add(createConcreteObservers());
        code.add(createConcreteSubject());

        return code;
    }

    public String getName() {
        return "Creational Patterns:Observer";
    }
}
