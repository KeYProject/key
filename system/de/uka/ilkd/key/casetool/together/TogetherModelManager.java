// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together;

import java.io.File;
import java.net.URL;
import java.util.Map;
import java.util.WeakHashMap;

import tudresden.ocl.check.types.ModelFacade;
import de.uka.ilkd.key.casetool.HashMapOfClassifier;
import de.uka.ilkd.key.casetool.ModelManager;
import de.uka.ilkd.key.casetool.OCLModelFacade;
import de.uka.ilkd.key.casetool.UMLOCLModel;
import de.uka.ilkd.key.gui.ModelSourceSettings;
import de.uka.ilkd.key.gui.ProofSettings;
import de.uka.ilkd.key.util.KeYResourceManager;


/**
 * @deprecated
 */
public class TogetherModelManager implements ModelManager {

    public static final TogetherModelManager INSTANCE 
	= new TogetherModelManager();

    private static Map models = new WeakHashMap();

    private TogetherModelManager() {}

    public ModelFacade getModelFacade
	(String location, String modelId) {
	ModelFacade res = (ModelFacade) models.get(modelId);
	if (res!=null) return res;
	ModelSourceSettings mss
	    = ProofSettings.DEFAULT_SETTINGS.getModelSourceSettings();
	if ("0".equals(mss.getModelSource())) {
	    String xmifileURL = "file:"+location;
	    // copying the uml.dtd if needed
	    String dtdTargetPath = (new File(location)).getParent();
	    String resourceName="uml.dtd";
	    String dtdTargetName=resourceName;
	    KeYResourceManager.getManager().copyIfNotExists
		(TogetherModelManager.class, resourceName, dtdTargetPath+File.separator+dtdTargetName);
	    if (!(new File(location)).isFile()) {
		throw new RuntimeException
		    ("XMI file "+location
		     +" does not exist.\n"
		     +"Please use File | Export | Model to XMI File "
		     +"\nto create the XMI model file in the project directory."
		     +"\nAs alternative, you can use the TogetherCC model "
		     +"directly by "
		     +"\nchoosing `TogetherCC data? structure as UML model source"
		     +"\nfrom the KeY menu.");
	    }
	    URL xmiURL = null;
	    try {
		xmiURL = new URL(xmifileURL);
	    } catch (java.net.MalformedURLException e) {
		throw new IllegalArgumentException("XMI file location wrong");
	    }
	    try {
		res = tudresden.ocl.check.types.xmifacade.XmiParser.
		    createModel(xmiURL, xmifileURL);
	    } catch (org.xml.sax.SAXException e) {
		throw new IllegalArgumentException("Error in XMI file "+location
						   +"\n"+e.getMessage());
	    } catch (java.io.IOException e) {
		throw new IllegalArgumentException("Error reading model file "
						   +"\n"+e.getMessage());
	    }

	} else {
	    UMLOCLModel model = new UMLOCLTogetherModel(null);
	    HashMapOfClassifier classifiers = model.getUMLOCLClassifiers();
	    res = new OCLModelFacade(classifiers);		
	} 	
	if (modelId!=null) models.put(modelId, res);
	return res;
    }
	
}
