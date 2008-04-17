// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
package de.uka.ilkd.key.casetool;

import java.util.Iterator;
import java.util.LinkedList;

import tudresden.ocl.check.OclTypeException;
import tudresden.ocl.check.types.*;

public class UMLOCLClassifier implements Any {

    private String name;
    private String fullName;
    private HashMapOfFeatures features;
    private HashMapOfClassifier supertypes;
    private HashMapOfAssociations associations;

    private UMLOCLClassifier() {
    }

    public UMLOCLClassifier(String name, String fullName) {
        this.name = name;
        this.fullName = fullName;
        this.features = new HashMapOfFeatures();
        this.supertypes = new HashMapOfClassifier();
        this.associations = new HashMapOfAssociations();
    }


    /** add a behavioural feature (operation) or a structural
     * feature (attribute) to this classifier
     */
    public void addFeature(String key,
                           UMLOCLFeature feature) {
        features.putFeature(key, feature);
    }

    public void addAssociation(String key,
                               UMLOCLAssociation assoc) {
        associations.putAssociation(key, assoc);
    }

    public UMLOCLFeature getFeature(String key) {
        return features.getFeature(key);
    }

    public HashMapOfFeatures features() {
        return features;
    }

    public HashMapOfAssociations getAssociations() {
        return associations;
    }

    public UMLOCLAssociation getAssociation(String s) {
        if (this.getAssociations().containsKey(s)) {
            return (UMLOCLAssociation)this.associations.get(s);
        }

        // search for the association in the supertypes
        Iterator it = supertypes.values().iterator();
        UMLOCLClassifier c;
        while (it.hasNext()) {
            c = (UMLOCLClassifier)it.next();
            if (c.getAssociations().containsKey(s)) {
                return (UMLOCLAssociation)c.associations.get(s);
            }
        }
        return null;
    }

    public void addSupertype(String key,
                             UMLOCLClassifier supertype) {
        supertypes.putClassifier(key, supertype);
    }

    public HashMapOfClassifier getSupertypes() {
        return supertypes;
    }

    public boolean conformsTo(Type t) {
        if (t instanceof UMLOCLClassifier) {
            if (this.getName().equals(((UMLOCLClassifier)t).getName()))
                return true;
            else
                return supertypes.containsKey(((UMLOCLClassifier)t).getName());
        }
        return false;
    }

    public boolean hasState(String stateName) {
        return false;
    }

    public Type navigateQualified(String name,
                                  Type[] qualifiers) {
        // ??? this check is from an example in the Dresden package ???
        if (qualifiers!=null)
            for (int i=0; i<qualifiers.length; i++)
                System.out.println(qualifiers[i]);
        if (qualifiers!=null && qualifiers.length>0)
            throw new OclTypeException("Feature \""+name+"\" of type "+
                                       this+" cannot be accessed with qualifier");

        Type ret=null;
        ret=Basic.navigateAnyQualified(name, this, qualifiers);
        if (ret!=null) {
            return ret;
        }
        if (getFeature(name)!=null)
            ret=getFeature(name).getType();
        else if (getAssociation(name)!=null) {
            ret=getAssociation(name).getTarget();
            if (getAssociation(name).getTargetMultiplicity().getMax()!=1) {
                ret=new Collection(Collection.SET, ret);
            }
        }
        if (ret==null) {
            throw new OclTypeException(this.name+" has no feature "+name);
        }
        return ret;
    }

    /**
     * @param params an array of Type (null is not allowed)
     */
    public Type navigateParameterized(String name,
                                      Type[] params) {
        
        assert params != null : "param should not be null";
        
        if (params.length==1 && params[0]!=null &&
            params[0] instanceof OclType) {
            if (name.equals("oclIsKindOf") ||
                name.equals("oclIsTypeOf"))
                return Basic.BOOLEAN;
            else if (name.equals("oclAsType"))
                return ((OclType)params[0]).getType();
        }

        String nameString = new String(name + "(");
        Iterator it;
        LinkedList candidates = new LinkedList();
        for (int i=0; i<params.length; i++) {
            if (params[i] instanceof UMLOCLClassifier) {
                if (i < params.length - 1) {
                    nameString = nameString + ((UMLOCLClassifier)params[i]).getName() + ",";
                } else {
                    nameString = nameString + ((UMLOCLClassifier)params[i]).getName();
                }
            } else {
                String s = new String();
                if (params[i] == Basic.INTEGER) {
                    s = "int";
                } else if (params[i] == Basic.BOOLEAN) {
                    s = "boolean";
                } else if (params[i] == Basic.REAL) {
                    s = "double";
                } else if (params[i] == Basic.STRING) {
                    s = "java.lang.String";
                }

                if (i < params.length - 1) {
                    nameString = nameString + s + ",";
                } else {
                    nameString = nameString + s;
                }
            }
        }
        nameString = nameString + ")";

        it = features().keySet().iterator();
        while (it.hasNext()){
            String key = it.next().toString();
            if (features.get(key) instanceof UMLOCLBehaviouralFeature){
                if(key.substring(0,key.indexOf('(')).equals(name)){
                    candidates.addLast((UMLOCLFeature)features.get(key));
                }
            }
        }
        boolean fits = false;

        it = candidates.iterator();
        while (it.hasNext()) {
            UMLOCLBehaviouralFeature tbf = (UMLOCLBehaviouralFeature)it.next();
            Type[] featureParams=tbf.getParameters();
            fits = (params.length==featureParams.length);
            for (int i=0; fits && i<params.length; i++) {
                if (!params[i].conformsTo(featureParams[i]))
                    fits=false;
            }
            if (fits) {
                return tbf.getType();
            }
        }

        return null;
    }

    public boolean equals(Object o) {
        if (!(o instanceof UMLOCLClassifier)) {
            return false;
        }
        return this.getFullName().equals(((UMLOCLClassifier)o).getFullName());
    }

    public int hashCode() {
        return this.getFullName().hashCode();
    }

    public String getName() {
        return name;
    }

    public String getFullName() {
        return fullName;
    }

    public String toString() {
        return name;
    }

}



