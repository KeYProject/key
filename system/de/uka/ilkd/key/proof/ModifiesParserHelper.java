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
//
package de.uka.ilkd.key.proof;

import java.io.StringReader;
import java.util.Vector;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;


/**
 * Parses modifies clauses.
 * @deprecated
 */
public class ModifiesParserHelper {
    private final ModelMethod modelMethod;
    private final Services services;
    private final NamespaceSet nss;
    private final JavaInfo javaInfo;

    private ProgramVariable self;
    private ListOfProgramVariable params = SLListOfProgramVariable.EMPTY_LIST;

    private Namespace ns = new Namespace();

    /**
     * @deprecated
     */
    private SetOfTerm modifiesElements;


    public ModifiesParserHelper(ModelMethod modelMethod, Services services,
                                NamespaceSet nss) {
        this.modelMethod = modelMethod;
        this.javaInfo = services.getJavaInfo();
        this.services = services;
        this.nss = nss;
    }


    /**
     * @deprecated Use parseModifiesClause(String modifiesString) instead.
     */
    public void parseModifiesClauseToHashSet(String modifiesString){

        // create program variables for "self" and the parameters
        parseSignatureStringAndFillNamespace();

        // puts the parsed modifies clause into the set modifiesElements
        parseModifiesString(modifiesString);
    }

    /**
     * @deprecated Use parseModifiesClause(String modifiesString) instead.
     */
    public void parseModifiesClause(Namespace ns, String modifiesString){
        this.ns = ns;

        // create program variables for "self" and the parameters
        parseSignatureStringAndFillNamespace();

        // puts the parsed modifies clause into the set modifiesElements
        parseModifiesString(modifiesString);
    }


    public SetOfLocationDescriptor parseModifiesClause(String modifiesString) {
        // create program variables for "self" and the parameters
        parseSignatureStringAndFillNamespace();

        if(modifiesString == null || "".equals(modifiesString)) {
            return SetAsListOfLocationDescriptor.EMPTY_SET;
        }

        if(modelMethod.isQuery()) {
            // query but non-empty modifies string; not allowed to happen!
            JOptionPane.showMessageDialog
                (null, "Inconsistent Modifies Set",
                 "Non-empty modifies set but the method is a query!",
                 JOptionPane.ERROR_MESSAGE);
            throw new IllegalStateException
                ("Non-empty modifies set but the method is a query!");
        }

        Namespace originalProgramVariables = nss.programVariables();
        nss.setProgramVariables(ns);

        KeYParser parser = new KeYParser(
                    ParserMode.TERM,
                    new KeYLexer(new StringReader(modifiesString), null),
                    "",
                    TermFactory.DEFAULT,
                    services,
                    nss);
        SetOfLocationDescriptor result
                = SetAsListOfLocationDescriptor.EMPTY_SET;
        try {
            result = parser.location_list();
        } catch(antlr.RecognitionException e) {
            System.out.println("RecognitionException occurred");
            e.printStackTrace();
        } catch(antlr.TokenStreamException e) {
            System.out.println("TokenStreamException occurred");
            e.printStackTrace();
        } finally {
            nss.setProgramVariables(originalProgramVariables);
        }

        return result;
    }


    private void parseSignatureStringAndFillNamespace(){
        // create "self" and add it to the namespace
        self = new LocationVariable(new ProgramElementName("self"),
                                   javaInfo.getKeYJavaType
                                   (modelMethod.getContainingClass().getFullClassName()));
        ns.add(self);

        String signatureString = modelMethod.getCallSignature(false);

        // first extract the name of the method
        int index = signatureString.indexOf("(");
        signatureString = signatureString.substring(index+1).trim();

        // then extract the names and types of parameters
        index = signatureString.indexOf(")");
        String type = null;
        while (index > 0){
            String paramName;
            KeYJavaType paramType;

            index = signatureString.indexOf(":");
            paramName = signatureString.substring(0, index).trim();
            signatureString = signatureString.substring(index+1).trim();

            index = signatureString.indexOf(";");
            // index = -1 if there is no ";" in the string because we are
            // parsing the last element
            if (index < 0) {
                index = signatureString.indexOf(")");
                type = signatureString.substring(0, index).trim();
                // convert to KeYJavaType and add to the vector
                paramType = javaInfo.getKeYJavaType(type);

                // the ")" is at the very end of the string so don't add
                // 1 to the index in this case otherwise there is a string
                // out of bounds error
                // by this the index calculated below will be 0
                signatureString = signatureString.substring(index+0).trim();
            }
            else {
                type = signatureString.substring(0, index).trim();
                // convert to KeYJavaType and add to the vector
                paramType = javaInfo.getKeYJavaType(type);
                signatureString = signatureString.substring(index+1).trim();
            }
            index = signatureString.indexOf(")");

            // create the parameter variable and add it to the namespace
            ProgramVariable paramVar
                = new LocationVariable(new ProgramElementName(paramName),
                                      paramType);
            params = params.prepend(paramVar);
            ns.add(paramVar);
        }
    }


    /**
     * @deprecated
     */
    private void parseModifiesString(String modifiesString) {
        if (modelMethod.isQuery()) {
            // query and empty or non-existing modifies string;
            // make an empty modifies string
            if (modifiesString == null || "".equals(modifiesString)){
                modifiesString = "";
            }
            // query but non-empty modifies string; not allowed to happen!
            else {
                JOptionPane.showMessageDialog
                    (null, "Inconsistent Modifies Set",
                     "Non-empty modifies set but the method is a query!",
                     JOptionPane.ERROR_MESSAGE);
                throw new IllegalStateException
                    ("Non-empty modifies set but the method is a query!");
            }
        }
        // otherwise no changes need to be done

        if (modifiesString == null || "".equals(modifiesString)) {
            modifiesElements = SetAsListOfTerm.EMPTY_SET;
        } else {
            modifiesElements = useTermParser(modifiesString);
        }
    }


    /**
     * @deprecated
     */
    private SetOfTerm useTermParser(String modifiesString) {
        modifiesString = "{"+modifiesString+"}";
        Namespace originalProgramVariables = nss.programVariables();
	nss.setProgramVariables(ns);	    
	KeYParser parser = new KeYParser(ParserMode.TERM, new KeYLexer(new StringReader(modifiesString),null),"", 
					   TermFactory.DEFAULT, services, nss);
	SetOfTerm accessTerms = SetAsListOfTerm.EMPTY_SET;
	try {
	    SetOfLocationDescriptor locs = parser.location_list();
	    IteratorOfLocationDescriptor it = locs.iterator();
	    while (it.hasNext()){
	    	accessTerms = accessTerms.add(((BasicLocationDescriptor)it.next()).getLocTerm());
	    }
	} catch( antlr.RecognitionException e0) {
	    System.out.println("RecognitionException occurred");
	    e0.printStackTrace();
	} catch(antlr.TokenStreamException e1) {
	    System.out.println("TokenStreamException occurred");
	    e1.printStackTrace();
	}
        nss.setProgramVariables(originalProgramVariables);
        return accessTerms;
    }

    /**
     * @deprecated
     */
    public SetOfTerm getModifiesElements(){
        return (modifiesElements == null ? SetAsListOfTerm.EMPTY_SET
                                         : modifiesElements);
    }

    public String getMethodName() {
        return modelMethod.getName();
    }


    public ProgramVariable getPVSelf(){
        return self;
    }


    public ListOfProgramVariable getPVParams(){
        return params;
    }


    /**
     * @deprecated
     */
    public Vector getPVVector(){
        Vector result = new Vector();
        IteratorOfProgramVariable it = params.iterator();
        while(it.hasNext()) {
            result.add(it.next());
        }
        return result;
    }


    /**
     * @deprecated
     */
    public Vector getParameterTypesVector(){
        Vector result = new Vector();
        IteratorOfProgramVariable it = params.iterator();
        while(it.hasNext()) {
            result.add(it.next().getKeYJavaType());
        }
        return result;
    }
}
