// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

/** @author Kristofer Johannisson */

package de.uka.ilkd.key.ocl.gf;

import java.io.BufferedOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;
import java.util.logging.Logger;

import tudresden.ocl.check.OclTypeException;
import tudresden.ocl.check.types.Type;

import com.togethersoft.openapi.rwi.*;

import de.uka.ilkd.key.casetool.*;


/** export UML/OCL type information to a file, for use in 
  * typechecking and with GF 
  */
public class ModelExporter {

    private static final String TOGETHER_UNIQUE_NAME_PREFIX = "<oiref:java#Class#";
    private static final String TOGETHER_UNIQUE_NAME_POSTFIX = ":oiref>";

    /** key: package name "java::lang", val: string of class signatures */
    private HashMap packClass;
    /** key: package name "java::lang", val: string of association signatures */
    private HashMap packAssoc;
    
    private HashMapOfClassifier model;

    /** Contains UMLOCLAssociation. Keeps track of which assocs have been added 
      * (necessary since otherwise
      * we get the same assoc twice, in both directions) */
    private Vector previousAssocs;

    private Logger logger;
    
    public ModelExporter(HashMapOfClassifier model)
    {
        logger = Logger.getLogger("key.ocl.gf");
        packClass = new HashMap();
        packAssoc = new HashMap();
        previousAssocs = new Vector();
        this.model = model;
    }
    
    /* @param s java-qualified class name e.g. java.lang.Object"
     * @return ocl type name e.g. "java::lang::Object", qualify with
     * "NOPACKAGE" as appropriate. 
     */
    private String javaType2oclType(String s)
    {   
        if (s.indexOf(".") > 0) { // qualified name
            return s.replaceAll("\\.","::");
        } else { // unqualified
            if (s.equals("Integer") || s.equals("Real") || s.equals("Boolean") ||
                s.equals("String")) {
                return s;
            } else {
                return "NOPACKAGE::" + s;
            }
        }
    }
    
    /* @param name possibly package-qualified name, with dots 
     * e.g. "java.lang.Object"
     * @return package in OCL notation, where dots are replaced with double
     * colons (last part discarded), e.g. "java::lang"
     */
    private String name2package(String name)
    {
        int lastDot = name.lastIndexOf(".");
        
        if (lastDot >= 0) {
            String javaPack = name.substring(0,lastDot);
            String result = javaPack.replaceAll("\\.","::");
            return result.equals("") ? "NOPACKAGE" : result;
        } else { // no dot found
            return "NOPACKAGE";
        }
    }
    
    private String qualifiedName(UMLOCLClassifier c)
    {
        return javaType2oclType(c.getFullName());
    }
    
    

    /** Convert a Type into a String representing an OCL type. This could 
      * entail qualifing and handling of array types
      */ 
    private String dresdenType2str(Type t)
    {
        if (t instanceof UMLOCLClassifier) {
            if (t.toString().endsWith("[]")) { // take care of broken array types
                String shortname = t.toString().substring(0, t.toString().length() - 2);
                String ocltype;
                try { // is the array element type a Java basic type?
                    ocltype = JavaOCLTypeMap.getBasicTypeFor(shortname).toString();
                } catch (OclTypeException ote) {
                    // if not, it could still be one of the following:
                    if (shortname.equals("String") || shortname.equals("Integer") ||
                        shortname.equals("Real") || shortname.equals("Boolean")) 
                    {
                        ocltype = shortname;
                    } else { // not a special class, qualify as usual:
                        ocltype = ((UMLOCLClassifier) t).getFullName();
                        ocltype = javaType2oclType(ocltype.substring(0, ocltype.length() - 2));
                    }
                }
                
                return "Sequence (" + ocltype +")";
            } 
            else { // not an array type
                return  qualifiedName( (UMLOCLClassifier) t); 
            }
        } 
        else { // this is probably a dresden Basic type
            return t.toString(); 
        }
    }
        
    
    private String structFeature2str(UMLOCLStructuralFeature attr)
    {
        if (classNotHandled(attr.getType().toString())) {
            return "";
        } else {
            return attr.getName() + " : " + dresdenType2str(attr.getType()) + ";\n";
        }
    }

    private boolean inhFromObject(UMLOCLFeature oper)
    {
        String n = oper.getName();
        Type r = oper.getType();
        String rS;
        if (r != null) {
            rS = r.toString();
        } else {
            rS = "";
        }
        
        return 
          (n.equals("wait()") && r == null) ||
          (n.equals("wait(long)") && r == null) ||
          (n.equals("wait(long,int)") && r == null) ||
          (n.equals("getClass()") && r == null) ||
          (n.equals("toString()") && rS.equals("String")) ||
          (n.equals("equals(java.lang.Object)") && rS.equals("Boolean")) ||
          (n.equals("hashCode()") && rS.equals("Integer")) ||
          (n.equals("notifyAll()") && r == null) ||
          (n.equals("finalize()")  && r == null) ||
          (n.equals("clone()") && rS.equals("Object")) ||
          (n.equals("notify()") && r == null);          
    }
    
    /** operation names contain parameters, this method cleans up the name,
      * i.e. it drops everything after (and including) the first '(' */
    private String dropArguments(String operName)
    {
        int x = operName.indexOf("(");
        if (x != -1) {
            return operName.substring(0,x);
        } else {
            return operName;
        }
    
    }

    private String behavFeature2str(UMLOCLBehaviouralFeature oper)
    {
        String result;
        String name = dropArguments(oper.getName());
        
        Type[] args = oper.getParameters();
        Type returns = oper.getType();
        
        // note that isQuery currently always returns true
        if (oper.isQuery() && returns != null) { 
            result = "{query} ";
        } else {
            result = "";
        }
        
        result += name + "(";
        for (int i=0; i < args.length; i++) {
            if (i != 0) { result += ", ";}
            if (classNotHandled(args[i].toString())) {
                 return "";
            }
            result += dresdenType2str(args[i]);
        }
        result += ")";
        
        if (returns != null) {
            if (classNotHandled(returns.toString())) {
                  return "";
            }
            result += " : " + dresdenType2str(returns);
        }
    
        result += ";\n";
        return result;
    }
    
    private String mult2str(Multiplicity mult)
    {
        int min = mult.getMin();
        int max = mult.getMax();

        
        if (min == 1  &&  max == 1) {
            return "[1]";
        } else { 
            String minS = "0"; // default in case of no match below
            String maxS = "*"; // default in case of no match below

            if (min == 0) {
                minS = "0";
            } else if (min == 1) {
                minS = "1";
            }
            if (max == 1) {
                maxS = "1";
            } else if (max == Multiplicity.INFINITE) {
                maxS = "*";
            }
            
            return "[" + minS + ".." + maxS + "]";
        }
    }

    // this really belongs in UMLOCLAssociations, but that is an interface
    private boolean assocEqualsNoDirection(UMLOCLAssociation a1, UMLOCLAssociation a2)
    {
        return (
            (
                a1.getSource() == a2.getSource() &&
                a1.getSourceMultiplicity() == a2.getSourceMultiplicity() &&
                a1.getSourceRole() == a2.getSourceRole() &&
                a1.getTarget() == a2.getTarget() &&
                a1.getTargetMultiplicity() == a2.getTargetMultiplicity() &&
                a1.getTargetRole() == a2.getTargetRole()
            )
            ||
            (
                a1.getSource() == a2.getTarget() &&
                a1.getSourceMultiplicity() == a2.getTargetMultiplicity() &&
                a1.getSourceRole() == a2.getTargetRole() &&
                a1.getTarget() == a2.getSource() &&
                a1.getTargetMultiplicity() == a2.getSourceMultiplicity() &&
                a1.getTargetRole() == a2.getSourceRole()
            )
        );
    }

    private boolean assocAlreadyDefined(UMLOCLAssociation assoc)
    {
        Iterator i = previousAssocs.iterator();
        UMLOCLAssociation a;
        
        while (i.hasNext()) {
            a = (UMLOCLAssociation) i.next();
            if (assocEqualsNoDirection(a, assoc)) {
                return true;
            }
        }
        
        return false;
    }
    
    private String getAssocQualifier(String sourceRole, String targetClass, String role, String qualifier)
    {
        //Added by Daniel
        //Checks if this association is ordered or not
        //as given by the "supplierQualifier"-property
        RwiModel rwiModel = RwiModelAccess.getModel();
        String result = "";
        //"targetClass" needs to be UMLOCLClassifier::getFullName() !
        String uniqueName = TOGETHER_UNIQUE_NAME_PREFIX + targetClass 
            + TOGETHER_UNIQUE_NAME_POSTFIX;
        RwiElement elem = rwiModel.findElement(uniqueName);
        if (elem != null) {
            RwiNode node = (RwiNode)elem;
            Enumeration memEnum = node.members();
            while (memEnum.hasMoreElements()) {
                RwiMember member = (RwiMember) memEnum.nextElement();
                String supplierRoleProp = member.getProperty(role);
                if (supplierRoleProp != null 
                    && supplierRoleProp.equals(sourceRole)) {
                    result = member.getProperty(qualifier);
                    break;
                }
            }
        }
        
        return result == null ? "" : result;
    }
    
    private String assoc2str(UMLOCLAssociation assoc)
    {   
        
        String sourceClass = assoc.getSource().getFullName(); 
        String targetClass = assoc.getTarget().getFullName(); 
        String sourceMult = mult2str(assoc.getSourceMultiplicity());
        String targetMult = mult2str(assoc.getTargetMultiplicity());
        String sourceRole = assoc.getSourceRole();      
        String targetRole = assoc.getTargetRole();

        String source, target;

        if (sourceRole != null) {
            source = sourceRole + " : " + 
                javaType2oclType(sourceClass) + " " + sourceMult;
        } else {
            source = javaType2oclType(sourceClass) + " " + sourceMult;
        }

        if (targetRole != null) {
            target = targetRole + " : " + javaType2oclType(targetClass)
                + " " + targetMult;
        } else {
            target = javaType2oclType(targetClass) + " " + targetMult;
        }
        
        // find out if the association-ends are {ordered} or not
        // N.B.: this requires role-names, will not work if they are missing
        // source/target might be client/supplier or supplier/client 
        // in Toghether-speak. Try both ways.
        String qLeft = getAssocQualifier(sourceRole, targetClass, "supplierRole", "supplierQualifier");
        String qRight = getAssocQualifier(sourceRole, targetClass, "supplierRole", "clientQualifier");

        if (qLeft.equals("") && qRight.equals("")) {
            qLeft = getAssocQualifier(targetRole, sourceClass, "supplierRole", "clientQualifier");
            qRight = getAssocQualifier(targetRole, sourceClass, "supplierRole", "supplierQualifier");
        }

        if (qLeft.equals("ordered") || qLeft.equals("{ordered}")) {
            source = "{ordered} " + source;
        }
        
        if (qRight.equals("ordered") || qRight.equals("{ordered}")) {
            target = "{ordered} " + target;
        }
        

        return source + " <-> " + target +";\n";
        
    }
    
    private String supertypes2str(HashMapOfClassifier supertypes)
    {
        String result = "";
        
        boolean addSeparator = false;
        Iterator i = supertypes.keySet().iterator();
        while (i.hasNext()) {
            if (addSeparator) {
                result += ", ";
            }
            UMLOCLClassifier classif = ((UMLOCLClassifier) supertypes.get(i.next()));
            result += qualifiedName(classif);
            addSeparator = true;
        }
        
        return result;
    }
    
    private boolean bracketed(String s)
    {
       return s.startsWith("<") && (
           s.endsWith(">") || s.indexOf(">(") != -1
       );
    }
    
    // we cannot handle all Java classes
    private boolean classNotHandled(String s)
    {
       return s.equals("Enumeration") || s.equals("Class") || s.equals("<Default>");
    }
    
    // some Java classes clash with built-in OCL types
    private boolean classAlreadyInOCL(String s)
    {
       return s.equals("Boolean") || s.equals("Integer") || 
           s.equals("String");
    }
    
    private void addClassifier(UMLOCLClassifier classif)
    {
        // array types are for some reason included by Together/KeY
        // do not include these
        if (classif.getName().endsWith("[]")) { 
            return;
        }
    
        if (classNotHandled(classif.getName()) || 
           classAlreadyInOCL(classif.getName())) {
           return;
        }
    
        HashMapOfClassifier supertypes = classif.getSupertypes();
        HashMapOfFeatures features = classif.features();
        HashMapOfAssociations assocs = classif.getAssociations();

        String pack = name2package(classif.getFullName());

        String supers = supertypes2str(supertypes);

        HashSet attrs = new HashSet();
        HashSet opers = new HashSet();
        
        Iterator i = features.keySet().iterator();
        while (i.hasNext()) {
            UMLOCLFeature f = (UMLOCLFeature) features.get(i.next());
            if (! bracketed(f.getName())) {
                if (f instanceof UMLOCLStructuralFeature) {
                    attrs.add(structFeature2str( (UMLOCLStructuralFeature) f));
                }
                else if (f instanceof UMLOCLBehaviouralFeature && (! inhFromObject(f)) ) {
                    opers.add(behavFeature2str( (UMLOCLBehaviouralFeature) f));
                }
            }
        }
        
        String assocsDef = "";
        i = assocs.keySet().iterator();
        while (i.hasNext()) {
            UMLOCLAssociation assoc = (UMLOCLAssociation) assocs.get(i.next());
            if (! assocAlreadyDefined(assoc)) {
                previousAssocs.add(assoc);
                assocsDef += assoc2str(assoc);
            }
        }
        if (! assocsDef.equals("")) {
            String assocsDefs = (String) packAssoc.get(pack);
            if (assocsDefs != null) {
                packAssoc.put(pack, assocsDefs + assocsDef);
            } else {
                packAssoc.put(pack, assocsDef);
            }
        }
        
        String attrsDef = "";
        i = attrs.iterator();
        while(i.hasNext()) {
          attrsDef += (String) i.next();
        }
        String opersDef = "";
        i = opers.iterator();
        while(i.hasNext()) {
          opersDef += (String) i.next();
        }
        
        String classDef = "<class> " + classif.getName()    + "\n" +
            (supers.equals("") ? "" : "<super> " + supers + " </super>\n") +
            (attrsDef.equals("")  ? "" : "<attributes> " + attrsDef + " </attributes>\n") +
            (opersDef.equals("")  ? "" :"<opers> " + opersDef + " </opers>\n") +
            "</class>\n";
        
        String classDefs = (String) packClass.get(pack);
        if (classDefs != null) {
            classDefs = classDefs + "\n" + classDef;
        } else {
            classDefs = classDef;
        }
        packClass.put(pack, classDefs);
    }

    /** export model information to a file
      * @param path path for what file to write to 
      */
    public void export(String path)
    {
        try {
            PrintStream stream = 
                new PrintStream(new BufferedOutputStream(new FileOutputStream(path)));
            export(stream);
            stream.flush();
            stream.close();
        } catch (FileNotFoundException e) {
            logger.severe("Can not open file " + path + " for writing model information.");
        }
        
    }
    
    /** export model information
      * @param ps export on this PrintStream
      */
    public void export(PrintStream ps)
    {
        Iterator i = model.keySet().iterator();
        while (i.hasNext()) {
            addClassifier( (UMLOCLClassifier) model.get(i.next()));
        }
        
        i = packClass.keySet().iterator();
        String pkg;

        while (i.hasNext()) {
            pkg = (String) i.next();
            ps.println("<package> " + pkg);
            
            ps.println( (String) packClass.get(pkg));
            ps.println();
            
            String pAssocs = (String) packAssoc.get(pkg);
            if (pAssocs != null) {
                ps.println("<associations>");
                //ps.println(orderAssocs(pAssocs));
		ps.println(pAssocs);
                ps.println("</associations>");
            }
            
            ps.println("</package>");
            ps.println();
        }
    }


    /*
    //To get all ordered associations to appear first
    public String orderAssocs(String str) {
    StringBuffer buffer = new StringBuffer(str);
    LinkedList list = new LinkedList();
    int index = buffer.indexOf("\n");
    while (index != -1) {
        String s = buffer.substring(0, index+1);
        list.add(s);
        buffer = buffer.delete(0, index+1);
        index = buffer.indexOf("\n");
    }

    StringBuffer result = new StringBuffer();
    Iterator iter = list.iterator();
    while (iter.hasNext()) {
        String s = (String)iter.next();
        if (s.startsWith("{ordered}")) {
        result.insert(0, s);
        } else {
        result.append(s);
        }
    }
    return result.toString();
    }
    */
}
