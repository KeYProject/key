// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

package de.uka.ilkd.key.casetool.together;

import java.io.File;
import java.util.Arrays;
import java.util.TreeSet;
import java.util.logging.Logger;

import de.uka.ilkd.key.ocl.gf.GFinterface;

/** control object interfacing KeY with GF */
public class TogetherGFInterface extends GFinterface
{

    public TogetherGFInterface()
    {
    	// set up logging
    	logger = Logger.getLogger("key.ocl.gf");
    	// Logger test = Logger.getRootLogger();
    	// test.error("GFinterface testing root logger...");
    
        // get the UML model

        projectRoot = UMLOCLTogetherModel.getTogetherProjectDir();
        model = new UMLOCLTogetherModel();
        modelInfoUmltypes = projectRoot + File.separator + modelinfoUmltypesFilename;

        // set up the filter (list) for features inherited from the java class "Object"
        String[] names = {"clone", "equals", "finalize", "getClass", "hashCode",
            "notify", "notifyAll", "toString", "wait"};
        fromObject = Arrays.asList(names);

        // set up list of types which should not be added to grammar even if
        // they occur in Java/UML model
        String[] types = {"OclType", "OclAny", "OclState", "OclExpression", "Real", "Integer", "String",
            "Boolean", "Bool", "boolean"}; // "Enumeration"
        inOCL = Arrays.asList(types);

        unknownAdded = new TreeSet();
    }

}
