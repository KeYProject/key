// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyPatternBase;

import java.io.*;
import java.util.Enumeration;
import java.util.Vector;

import javax.swing.JDialog;
import javax.swing.JOptionPane;

import com.togethersoft.modules.patterns.UNIVERSAL.PatternBaseException;
import com.togethersoft.modules.patterns.UNIVERSAL.PatternUIBuilder;
import com.togethersoft.openapi.ide.inspector.IdeInspector;
import com.togethersoft.openapi.ide.inspector.IdeInspectorProperty;
import com.togethersoft.openapi.ide.inspector.IdeInspectorPropertySetComponent;
import com.togethersoft.openapi.ide.inspector.util.editors.PropertyMapMultiValueElementChooserEditor;
import com.togethersoft.openapi.ide.inspector.util.property.PropertyMapInspectorProperty;
import com.togethersoft.openapi.ide.message.IdeMessageManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageType;
import com.togethersoft.openapi.ide.window.IdeSelectorDialogType;
import com.togethersoft.openapi.ide.window.IdeWindowManagerAccess;
import com.togethersoft.openapi.sci.*;
import com.togethersoft.openapi.sci.pattern.SciPatternProperty;
import com.togethersoft.openapi.sci.pattern.SciPatternUtil;
import com.togethersoft.openapi.util.propertyMap.Property;
import com.togethersoft.openapi.util.propertyMap.PropertyMap;
import com.togethersoft.openapi.util.propertyMap.PropertyMapListener;

import de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyParser.Entry;
import de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyParser.MyParser;
import de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyParser.ParseException;
import de.uka.ilkd.key.util.Debug;

public abstract class MyPatternBase extends com.togethersoft.modules.patterns.UNIVERSAL.PatternBase {


    private Vector additionalProperties = new Vector();
    private Vector constraintVector = new Vector();
    private Vector mappingVector = new Vector();
    private Vector mappingVectorTemp = new Vector();
    private Vector placeVector = new Vector();
    private Vector commentVector = new Vector();
    private final static String beginOfComment = "<!-- begin of my comments -->";
    protected static PropertyMap myProperties = null;
    protected static IdeInspector myIdeInspector = null;
    private Vector myAttributePropertyVector = new Vector();
    private static PatternUIBuilder myUIBuilder = null;
    private static Vector inspectorPropertiesVector=new Vector();
    private static String pageName="";


    public SciClass getSelectedClass() {
        Object selectedObject = getProperties().getPropertyValue(SciPatternProperty.ELEMENT);
        if (selectedObject != null && selectedObject instanceof SciClass) {
            return (SciClass)selectedObject;
        }
        else {
            return null;
        }
    }

    public SciOperation getSelectedMethod(){
	Object selectedObject = getProperties().getPropertyValue(SciPatternProperty.ELEMENT);
	//	System.out.println("Object: "+selectedObject.toString());
	if (selectedObject != null && selectedObject instanceof SciOperation) {
            return (SciOperation)selectedObject;
        }
        else {
            return null;
        }
    }


    public SciAttribute getSelectedAttribute(){
	Object selectedObject = getProperties().getPropertyValue(SciPatternProperty.ELEMENT);
	if (selectedObject != null && selectedObject instanceof SciAttribute) {
            return (SciAttribute)selectedObject;
        }
        else {
            return null;
        }
    }

    
    public MyPatternBase(){
	super();
	if (myProperties == null)
	    myProperties = getProperties();
	if (myIdeInspector == null)
	    myIdeInspector = getIdeInspector();
    }


    public void addPropertyMapListener(String name, PropertyMapListener listener) {
        myProperties.addPropertyMapListener(name, listener);
    }

    protected void addToPropertiesVector(Vector v){
	for (int i=0; i<v.size(); i++)
	    inspectorPropertiesVector.addElement(v.elementAt(i));
    }


    protected boolean removeFromPropertiesVector(String s){
	for (int i=0; i<inspectorPropertiesVector.size(); i++){
	    if (inspectorPropertiesVector.elementAt(i).toString().equals(s)){
		inspectorPropertiesVector.removeElementAt(i);
		return true;
	    }
	}
	return false;
    }
  
    protected void setUIBuilder(PatternUIBuilder builder){ 
	myUIBuilder = builder;
    }

    protected void setPageName(String name){
	pageName = name;
    }

    protected String classNameShouldBeCorrect(String propertyName) throws MyPatternBaseException {
        String result = getStringPropertyValue(propertyName);
        if (result == null || result.length() == 0) {
            Object[] arguments = { propertyName };
            String message = createTextByPattern("{0} should be defined.", arguments);
            throw new MyPatternBaseException(message);
        }
        return checkStringValue(result, true);
    }

    protected String checkStringValue(String value, boolean isClassName) throws MyPatternBaseException {
        String identifier = value;
        if (isClassName && SciLanguage.JAVA.equals(getLanguage())) {
            int lastIndex = identifier.lastIndexOf('.');
            if (lastIndex >= 0) {
                String packageName = identifier.substring(0, lastIndex);
                if (EMPTY_STRING.equals(packageName) || (getModel().findClass(getLanguage(), packageName) == null &&
							 getModel().findPackage(packageName) == null)) {
                    Object[] arguments = { packageName };
                    String message = createTextByPattern("Container \"{0}\" not found.", arguments);
                    throw new MyPatternBaseException(message);
                }
                identifier = identifier.substring(lastIndex + 1);
            }
        }

        if (!getLanguageHelper().isValidIdentifier(identifier)) {
            Object[] arguments = { identifier };
            String message = createTextByPattern("\"{0}\" is invalid identifier.", arguments);
            throw new MyPatternBaseException(message);
        }

        return value;
    }


    protected void addBooleanFieldItem(String name, boolean initialValue) {
	//	if (myUIBuilder==null)
	//    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "myUIBuilder ist null!!!\n");
	try{
	    if (myUIBuilder.addPropertyToPage(pageName, name, name, PatternUIBuilder.PropertyType.Boolean) == null) {
		throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
	    }
	    if (initialValue)
		setPropertyValue(name,Boolean.TRUE);
	    else
		setPropertyValue(name,Boolean.FALSE);
	    inspectorPropertiesVector.addElement(name);
	    myUIBuilder.setCreatedPatternUI();
	}
	catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }

    }


    protected void addBooleanFieldItem(String name, boolean initialValue, 
            MyCondition condition) {
        IdeInspectorProperty property = new 
        PropertyMapInspectorProperty(getProperties(), name, Boolean.class);	  
        property.setName(name);
        if (initialValue)
            setPropertyValue(name,Boolean.TRUE);
        else
            setPropertyValue(name,Boolean.FALSE);
        inspectorPropertiesVector.addElement(name);
        myUIBuilder.setCreatedPatternUI();
        IdeInspectorPropertySetComponent propertyPage = (IdeInspectorPropertySetComponent) 
        getIdeInspector().findComponent(pageName);
        if (propertyPage == null) {
            return;
        }

        propertyPage.addProperty(property, condition);	    
        ((IdeInspectorPropertySetComponent)   
                getIdeInspector().findComponent(pageName)).update();	    
    }


    protected boolean isBooleanFieldSelected(String name) {
	if ( "true".equals ( getPropertyValue ( name ).toString () ) )
	    return true;
	else
	    return false;
    }


    protected void addStringFieldItem(String name) {
	//	if (myUIBuilder==null)
	//    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "myUIBuilder ist null!!!\n");
	try{
	    if (myUIBuilder.addPropertyToPage(pageName, name, name, PatternUIBuilder.PropertyType.String) == null) {
		throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
	    }
	    inspectorPropertiesVector.addElement(name);
	    myUIBuilder.setCreatedPatternUI();
	}
	catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }

    protected void addStringFieldItem(String name, MyCondition condition) {
        IdeInspectorProperty property = new PropertyMapInspectorProperty(getProperties(), name, String.class);	  
        property.setName(name);
        inspectorPropertiesVector.addElement(name);
        myUIBuilder.setCreatedPatternUI();
        IdeInspectorPropertySetComponent propertyPage = (IdeInspectorPropertySetComponent) 
        getIdeInspector().findComponent(pageName);
        if (propertyPage == null) {
            return;
        }

        propertyPage.addProperty(property, condition);	    
        ((IdeInspectorPropertySetComponent)   
                getIdeInspector().findComponent(pageName)).update();

    }


    protected void addClassPropertyItem(String name, boolean allowInterface, boolean multiple) {
	//if (myUIBuilder==null)
	//    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "myUIBuilder ist null!!!\n");
	int m = 0;
	if (multiple)
	    m = PatternUIBuilder.PropertyType.MultiValue;
	else
	    m = PatternUIBuilder.PropertyType.SingleValue;
	try{
	    if (myUIBuilder.addClassPropertyToPage(pageName, name, name, m , allowInterface) == null) {
		throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
	    }
	    inspectorPropertiesVector.addElement(name);
	    myUIBuilder.setCreatedPatternUI();
	}
	catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }


    // wenn der Benutzer nicht in der Combobox rumklickt, dann wird als Element null 
    // zurueckkgeliefert!!! Um das zu vermeiden, muss in der prepare-methode in Pattern.java
    // von Hand mit setPropertyValue initialisiert werden. Das setPropertyValue hier bringt
    // nichts!!!
    protected void addComboboxFieldItem(String name, Vector values, String defaultValue) {
	//if (myUIBuilder==null)
	//    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "myUIBuilder ist null!!!\n");
	try{
	    if (myUIBuilder.addPropertyToPage(pageName, name, name, PatternUIBuilder.PropertyType.StringChooser, values.toArray() ) == null) {
		throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
	    }
	    setPropertyValue(name, defaultValue);
	    inspectorPropertiesVector.addElement(name);
	    myUIBuilder.setCreatedPatternUI();
	}
	catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }



    protected void initializeInspector() {
        try {
            myUIBuilder = null;
            myUIBuilder = createUIBuilder(true);

	    // Create page
            if (myUIBuilder.addInspectorPage(pageName, PatternUIBuilder.UIPresentation.Table) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            
            myUIBuilder.setCreatedPatternUI();
        }
        catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }

    public void showItem(String name, boolean show) {
	
	//myProperties.setPropertyValue(getIdeInspector()+ ".item." + name + ".condition", (new Boolean(show)).toString());
	// weiss nicht, wie das unter TJ4.0 funktioniert
	enableItem(name, show);
    }


    public void showItem(String name, boolean show, MyCondition condition) {
	
	//myProperties.setPropertyValue(getIdeInspector()+ ".item." + name + ".condition", (new Boolean(show)).toString());
	// weiss nicht, wie das unter TJ4.0 funktioniert
	//enableItem(name, show);

	IdeInspectorPropertySetComponent propertyPage = (IdeInspectorPropertySetComponent) 
	    getIdeInspector().findComponent(pageName);
	if (propertyPage == null) { 
            return;
        }
        IdeInspectorProperty property = propertyPage.findProperty(name);
	if (property == null) {
	    return;
	}

	//	System.out.println("Fuege jetzt die condition hinzu");
	condition.setFlag(show);
	propertyPage.addProperty(property, condition);	 
	((IdeInspectorPropertySetComponent)   
	 getIdeInspector().findComponent(pageName)).update();
	
    }


    public boolean isItemShown(String name) {
	if ("true".equals ( getPropertyValue ( name ).toString () ) )
	    return true;
	else
	    return false;
    }


   
    public void setMultiple(String item, boolean on) {
	// wei� noch nicht, wie das geht. Stimmt so nicht
	Enumeration enum1 = getProperties().properties(item);
	if (on){
	    while (enum1.hasMoreElements()) {
		IdeInspectorProperty property = (IdeInspectorProperty)enum1.nextElement();
		String name = (String)property.getValue();
		property.setPropertyEditor(new PropertyMapMultiValueElementChooserEditor(null, item,IdeSelectorDialogType.MULTIPLE_CLASSES));
		//		System.out.println(name);
	    }	    
	}
	else{
	    while (enum1.hasMoreElements()) {
		IdeInspectorProperty property = (IdeInspectorProperty)enum1.nextElement();
		String name = (String)property.getValue();
		property.setPropertyEditor(new PropertyMapMultiValueElementChooserEditor(null, item,IdeSelectorDialogType.CLASSES));
		//		System.out.println(name);
	    }
	}
	    
    }


    public boolean isMultiple(String item){
	if (item!=null){
	    if ( getPropertyValue(item) != null &&
		 "true".equals ( getPropertyValue(item).toString() ) ) 
		return true;
	    else
		return false;
	}
	else
	    return false;
    }


    public void showItemVector(Vector v, String oclScheme, boolean show) {
	for (int i=0; i<v.size(); i=i+3) {
	    if (((String)(v.elementAt(i))).equals(oclScheme)) {
		if ( "visible".equals ( v.elementAt(i+1) ) ) 
		    showItem((String)v.elementAt(i+2), show);
		if ( "multiple".equals ( v.elementAt ( i+1 ) ) ) 
		    setMultiple((String)v.elementAt(i+2), show);
	    }
	}
	
    }
    

    public void copySpecFromTo(SciClass sc, String tm, SciClass tc){
	Enumeration opEnum = sc.operations();
	SciOperation op;
	while (opEnum.hasMoreElements()){
	    op = (SciOperation)opEnum.nextElement();
	    if (tm.equals(op.getName())){
		String pre =op.getTagList().getTagValue("preconditions");
		String post=op.getTagList().getTagValue("postconditions");
		
		Enumeration targetOpEnum = tc.operations();
		SciOperation top;
		while (targetOpEnum.hasMoreElements()){
		    top = (SciOperation)targetOpEnum.nextElement();
		    if (tm.equals(top.getName())){
			top.getTagList().setTagValue("preconditions",pre);
			top.getTagList().setTagValue("postconditions",post);
			
		    }
		}		
	    }			 
	}
    }

    
    protected void initPattern(){
		
	// read OCL-Schemes from file 
	
	final Vector oclSchemeVector = new Vector();
	final Vector oclSchemeNamesVector = new Vector();
	final String patternTopPath = System.getProperty("key.pattern.path");	
	final String[] extensions = {".ocl"};	
	String classname = getClass().getName().replace('.',File.separatorChar);	
	String path = patternTopPath + File.separator + classname.substring
	    (0, classname.lastIndexOf ( File.separatorChar ) );
	String oclPath = path + File.separator + "OCL";
System.out.println( "Pattern Path:" + path );	
	commentVector.removeAllElements();
	additionalProperties.removeAllElements();
	constraintVector.removeAllElements();
	mappingVector.removeAllElements();
	placeVector.removeAllElements();
	
	try{
	    int data;
	    String dummy="";
	    // check, if the directory for OCL-SCHEMES does exist
	    File oclSchemeDir = new File(oclPath);
	    if ((oclSchemeDir.exists()) && oclSchemeDir.isDirectory()){
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "Verzeichnis existiert!!!");
		// get list with files in this directory
		String[] fileList = oclSchemeDir.list(new FilenameFilter(){
			public boolean accept(File f, String name){
			    int length = name.length(); 
			    for (int i = 0 ; i < extensions.length; i++) { 
				String ext = extensions[i]; 
				if (name.endsWith(ext) && name.charAt(length - ext.length()) == '.') {
				    return true; 
				} 
			    } 
			    return false;
			}
		    });

		String fileInputPath = oclPath;	

		for (int i=0; i<fileList.length; i++){
		    FileInputStream fileInput = new FileInputStream(new File(fileInputPath, fileList[i]));
		  
		    //  InputStream from file to parser
		    MyParser parser = new MyParser((InputStream)fileInput);
		    try{
			// add a checkbox (initially false), so that the user can select this OCL-Scheme. 
			addBooleanFieldItem(fileList[i].substring(0,fileList[i].length()-4),false);
			myUIBuilder.assignListenedInspectorProperties(inspectorPropertiesVector);
			parser.parse( fileList[i].substring(0,fileList[i].length()-4) );
			mappingVectorTemp = parser.getMappingVector();
			for (int z=0; z<mappingVectorTemp.size(); z++)
			    mappingVector.addElement(mappingVectorTemp.elementAt(z));
			// add the parsed additional properties to the vector in which all additional props. are stored
			for (int z=0; z<parser.getAdditionalPropertiesVector().size(); z++)
			    additionalProperties.addElement(parser.getAdditionalPropertiesVector().elementAt(z));
			for (int z=0; z<parser.getPlaceVector().size(); z++)
			    placeVector.addElement(parser.getPlaceVector().elementAt(z));
			for (int z=0; z<parser.getConstraintVector().size(); z=z+2){
			    constraintVector.addElement(fileList[i].substring(0,fileList[i].length()-4));			    
			    constraintVector.addElement(parser.getConstraintVector().elementAt(z));
			    constraintVector.addElement(parser.getConstraintVector().elementAt(z+1));
			}
			commentVector.addElement(parser.getCommentString());
		    }
		    catch (ParseException parseError){
			IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "Parse error in file "+fileList[i]+": "+parseError.toString());
			// parse error, so remove
			getProperties().setPropertyValue("inspector.item." + fileList[i], "");
		    }
       
		    fileInput.close();
		    fileInput = new FileInputStream(new File(fileInputPath, fileList[i])); 


		    // read OclScheme
		    dummy="";
		    Vector puffer = new Vector();
		    while ((data = fileInput.read()) != -1){
			if ((char)data=="\n".charAt(0)) {
			    puffer.addElement(dummy);
			    dummy="";
			}
			else
			    dummy = dummy + "" + (char)data;
			// IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,data+";");
		    }

		    fileInput.close();

		    if (!puffer.isEmpty()){
			// print input-files
			for (int j=0; j<puffer.size();j++)
			    //			    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, puffer.elementAt(j).toString());
			
			    oclSchemeNamesVector.addElement(fileList[i]); // name of ocl-scheme
			oclSchemeVector.addElement(puffer);           // Stringrepresentation of ocl-scheme as a Vector of Strings
		    }

		}
	    }
	    else
		IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "Verzeichnis "+oclPath+" existiert nicht!!!");
	}
	catch(FileNotFoundException e){
	    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "File "+e.toString()+" not found!");
	}
	catch(IOException ioe){
	    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "IOException");
	}
	
	// manipulate Desciption.html
	
	try{
	    //	     IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "bearbeite jetzt description!\n");
	    RandomAccessFile descriptionFile = new RandomAccessFile(path + File.separatorChar + "Description.html", "rw");
	    String line="";
	    boolean found = false;
	    while ((line=descriptionFile.readLine())!=null)
		if (line.equals(beginOfComment)){
		    found = true;
		    //		    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "Kommentar gefunden!\n");
		    descriptionFile.writeBytes("<h3>Documentation of OCL-Schemata</h3>");
		    for (int y=0; y<commentVector.size(); y++){
			if ( ! "".equals ( commentVector.elementAt ( y ) ) )
			    descriptionFile.writeBytes("<ul>"+commentVector.elementAt(y).toString()+"</ul>");
			//			IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "Kommentar: "+commentVector.elementAt(y).toString());
		    }
		    //descriptionFile.writeBytes("</body>");
		    //descriptionFile.writeBytes("</html>");
		    descriptionFile.setLength(descriptionFile.getFilePointer());
		}
	    if (!found){
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "Kommentar nicht gefunden!\n");
		descriptionFile.seek(descriptionFile.length());
		descriptionFile.writeBytes(beginOfComment+"\n");
		descriptionFile.writeBytes("<h3>Documentation of OCL-Schemata</h3>");
		for (int y=0; y<commentVector.size(); y++){
		    if ( ! "".equals ( commentVector.elementAt(y) ) )
			descriptionFile.writeBytes("<ul>"+commentVector.elementAt(y).toString()+"</ul>");
		}
		//descriptionFile.writeBytes("</body>");
		//descriptionFile.writeBytes("</html>");
		descriptionFile.setLength(descriptionFile.getFilePointer());
	    }
	    descriptionFile.close();
	}
	catch(FileNotFoundException e){
	    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "File not found: "+e);
	}
	catch(IOException ioe){
	    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL, "IOException");
	}
	
	
	//IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "PARSEN UND EINLESEN BEENDET\n");
	
       	myUIBuilder.assignListenedInspectorProperties(inspectorPropertiesVector);
	
    }
    


    protected Vector extractParameter(String paraList){
	Vector v = new Vector();
	int pos = 0;
	int endpos = 0;
	String dummy;
	if (paraList.length() > 0) {
	    while (pos >= 0) {
		endpos = paraList.indexOf(",", pos);
		if (endpos >= 0){
		    dummy =  (new StringBuffer(paraList)).substring(pos, endpos).trim();
		    if (dummy.indexOf(" ") != -1){
			dummy = dummy.substring(dummy.indexOf(" ")).trim();
		    }
		    v.addElement(dummy);
		    pos = endpos+1;
		}
		else {
		    dummy = (new StringBuffer(paraList)).substring(pos).trim();
		    if (dummy.indexOf(" ") != -1){
			dummy = dummy.substring(dummy.indexOf(" ")).trim();
		    }
		    v.addElement(dummy);
		    pos = -1000;
		}
	    }
	
	    return v;
	}
	else
	    return null;
    }



    // only a wrapper-method
    protected void applyOCLSchemes(){
	applyOCLSchemeAdjustments(additionalProperties, constraintVector );	
	applyOCLConstraints(additionalProperties, constraintVector, mappingVector, placeVector);
    }


    // this method adds the classes, methods, etc., that were defined in the OCLScheme to the UML-diagram
    protected void applyOCLSchemeAdjustments(Vector additionalProps, Vector constraintVector){
        SciClass cls;
        for (int i=0; i<additionalProps.size(); i++) {
	    //	    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,((Entry)additionalProps.elementAt(i)).toString() );
            // test, whether canHaveSeveralSubclasses is added and whether it is selected (selected <-> visible)
            if ( "canHaveSeveralSubclasses#".equals 
		 ( ( ( Entry ) additionalProps.elementAt ( i ) ).getProperty () ) 
                 && (isBooleanFieldSelected( ((Entry)additionalProps.elementAt(i)).getOclSchemeName()) ) ) {
                Enumeration en = propertiesEnumeration(((Entry)additionalProps.elementAt(i)).getPropertyName());
                while (en.hasMoreElements()) {
                    Property property = (Property)en.nextElement();
                    String name = (String)property.getValue();
                    cls = getClassByName(name, false);
                    try{
			SciPatternUtil.createInheritance(cls, findClassByName( classNameShouldBeCorrect(((Entry)additionalProps.elementAt(i)).getName())  ) );
		    }
		    catch(MyPatternBaseException e) 
			{Debug.out("Exception thrown by class MyPatternBase at createInheritance");}
		}
            }
            // is there "canHaveMultipleInstances#"?
            if ( "canHaveMultipleInstances#".equals 
		 ( ( ( Entry ) additionalProps.elementAt ( i ) ).getProperty () ) &&
                 isMultiple ( ( ( Entry ) additionalProps.elementAt ( i ) ).getName()) ) {
                Enumeration enum2 = propertiesEnumeration(((Entry)additionalProps.elementAt(i)).getName());
                while (enum2.hasMoreElements()) {
                    Property property = (Property)enum2.nextElement();
                    String name = (String)property.getValue();
                    
                    // create a copy of the class, that can have multiple instances, because the other instances 
                    // should have the same behaviour

                    // does the class already exist?
                    if (findClassByName(name)==null) {
                        try{
                            SciClass cpy = (SciClass)findClassByName( classNameShouldBeCorrect(((Entry)additionalProps.elementAt(i)).getName()) ).copy();
                            // change name of cpy
                            cpy.setName(name);
                            // paste it in container (it becomes visible)
                            getContainer().paste(cpy,null,false);
                        }
                        catch (MyPatternBaseException e) 
			    {Debug.out("Exception thrown by class MyPatternBase at findClassByName");}
                    }
                    
                }
            }

	    // is there "addClassAttribute#"?
            if ( "addClassAttribute#".equals ( ( ( Entry ) additionalProps.elementAt ( i ) ).getProperty () )
		 && isBooleanFieldSelected( ((Entry)additionalProps.elementAt(i)).getOclSchemeName()) ) {
                
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Versuche jetzt, ord einzuf�gen!!!\n" );
		String dummy = ((Entry)additionalProps.elementAt(i)).getName();
		int separator1 = dummy.indexOf("#");
		
		String className = dummy.substring(0, separator1);
		String type = dummy.substring(separator1+1,dummy.length());
		    
		SciAttribute newAttribute = SciModelAccess.getModel().getFactory(SciLanguage.JAVA).newAttribute(); 
		newAttribute.setName(getStringPropertyValue(((Entry)additionalProps.elementAt(i)).getPropertyName()));
		
		newAttribute.setProperty(SciProperty.STATIC, true); //making it static
		newAttribute.getType().setText(type); //setting the type
		newAttribute.setProperty(SciProperty.PUBLIC, true); //setting the public modifier
		//pasting it into someSciClass		   
		try {
		    //		    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Bin bei addClassAttribute: className :" +className+"\n" );
                    ((SciClass)findClassByName( classNameShouldBeCorrect(className) )).paste(newAttribute, null, false);
                }
                catch (MyPatternBaseException e) 
		    {Debug.out("Exception thrown by class MyPatternBase at findClassByName");}
	    }
	    

	    // is there "addMethod"?
            if ( "addMethod#".equals 
		 ( ( ( Entry ) additionalProps.elementAt ( i ) ).getProperty () ) &&
		 isBooleanFieldSelected ( ( ( Entry ) additionalProps.
					  elementAt ( i ) ).getOclSchemeName () ) ) {

		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"erstelle gerade Method" );
                SciOperation method = getFactory().newOperation();
                method.setName(getStringPropertyValue(((Entry)additionalProps.elementAt(i)).getPropertyName()));
                method.getReturnType().setText("void");
                method.setProperty(SciProperty.PUBLIC, true);
                // paste the new method in the modell
                try {
                    ((SciClass)findClassByName( classNameShouldBeCorrect(((Entry)additionalProps.elementAt(i)).getName()) )).paste(method, null, false);
                }
                catch (PatternBaseException e) 
		    {Debug.out("Exception thrown by class MyPatternBase at findClassByName");}
            }
            
        
        }
    }



	
    // add the ocl-constraints that were specified in the OCL-scheme
    protected void applyOCLConstraints( Vector additionalProps, Vector constraintVector, Vector mappingVector, Vector placeVector ) {
	StringBuffer stringBuffer;
	String newString;
	String s;
	int start, length;
	boolean selectedClassFound = false;
	boolean fehler = false;
	for (int i=0; i<constraintVector.size(); i=i+3) {
	    //is scheme selected?
	    if (isBooleanFieldSelected((String)constraintVector.elementAt(i))) {
		fehler = false;
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Ocl-Constraint "+(String)constraintVector.elementAt(i)+" mit folgenden Mappings ausgew�hlt:\n"); 
		stringBuffer = new StringBuffer(constraintVector.elementAt(i+1).toString());
		selectedClassFound = false;
		for (int j=0; j<mappingVector.size(); j=j+3){
		    //		    System.out.println("Vergleich: "+mappingVector.elementAt(j).toString()+":"+constraintVector.elementAt(i).toString()+"\n");
		    if (mappingVector.elementAt(j).toString().equals(constraintVector.elementAt(i).toString())) {
			
			//			System.out.println("EINS\n");

			//			IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,mappingVector.elementAt(j)+" : "+ mappingVector.elementAt(j+1)+" : "+mappingVector.elementAt(j+2).toString().trim()+" : "+getStringPropertyValue(mappingVector.elementAt(j+2).toString().trim())+"\n"); 
			
			//			System.out.println(mappingVector.elementAt(j+1).toString());

			//------------------------------------------------
			// sonderparameter pr�fen

			newString=null;

			if ( "selectedMethod".equals ( mappingVector.elementAt(j+1).toString() ) ) {
			    //			    System.out.println("ZWEI\n");
			    String str1 = constraintVector.elementAt(i+1).toString();
			    if ((str1 != null) && (str1.indexOf("selectedMethod") >= 0)){
				//				System.out.println("bin bei selectedMethod\n");
				if (getSelectedMethod()!=null){
				    s = getSelectedMethod().toString();
				    //newString = s.substring( s.indexOf("Class#")+6, s.indexOf(":",s.indexOf("Class#")));
				    selectedClassFound = true;
				    setPropertyValue(mappingVector.elementAt(j+2).toString(),getSelectedMethod().getContainingClass().getQualifiedName());
				    newString = s;
				    //				    System.out.println("gew�hlte Methode: "+s+"in der Klasse: "+getStringPropertyValue(mappingVector.elementAt(j+2).toString())+"\n");				       
				}
			    }
			}
			
			if ( "selectedAttribute".equals ( mappingVector.elementAt(j+1).toString () ) ) {
			    //			    System.out.println("DREI\n");
			    String str5 = constraintVector.elementAt(i+1).toString();
			    if ((str5 != null) && (str5.indexOf("selectedAttribute") >= 0)){
				//				System.out.println("bin bei selectedAttribute\n");
				if (getSelectedAttribute() !=null){
				    s = getSelectedAttribute().toString();
				    //newString = s.substring( s.indexOf("Class#")+6, s.indexOf(":",s.indexOf("Class#")));
				    selectedClassFound = true;
				    setPropertyValue(mappingVector.elementAt(j+2).toString(),getSelectedMethod().getContainingClass().getQualifiedName());
				    newString = s;
				    //				    System.out.println("gew�hltes Attribute: "+s+"\n");				       
				}
			    }
			}
			


			
			if ( "selectedClass".equals ( mappingVector.elementAt ( j+1 ).toString() ) && 
			     ! selectedClassFound  ) {
			    //			    System.out.println("VIER\n");
			    String str3 = constraintVector.elementAt(i+1).toString();
			    //			    System.out.println(str3);
			    if (str3 != null){
				//				System.out.println("VIER-EINS\n");
				if (getSelectedClass()!=null){
				    //				    System.out.println("VIER-ZWEI\n");
				    s = getSelectedClass().toString();
				    selectedClassFound = true;
				    newString = s.substring( s.indexOf("Class#")+6, s.indexOf(":",s.indexOf("Class#")));
				    setPropertyValue(mappingVector.elementAt(j+2).toString(),newString);
				}
				else {
				    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL,"Please first select a class before applying this pattern!");
				}
			    }
			}	       
			
			if ( "selectedParameter".equals ( mappingVector.elementAt ( j+1 ).toString () ) ) {
			    //			    System.out.println("F�NF\n");
			    String str2 = constraintVector.elementAt(i+1).toString();
			    if ((str2 != null) && (str2.indexOf("selectedParameter") >= 0)){
				String paraList="";
				if (getSelectedMethod() != null)
				    paraList = getSelectedMethod().getParameterList().getText();
				//				System.out.println("paraString: "+paraList+"\n");
				Vector v = new Vector();				    
				v = extractParameter(paraList);
				if ( v != null ) {
				    if (v.size() > 1){
					Object[] possibleValues = v.toArray();
					JDialog jdialog = IdeWindowManagerAccess.getWindowManager().createDialog(null);
					JOptionPane pane = new JOptionPane();
					jdialog = IdeWindowManagerAccess.getWindowManager().createDialog(null);
					//jdialog = pane.createDialog(null, "titel");	      
					Object selectedValue = JOptionPane.showInputDialog(null, 
										    "Choose a parameter", "",JOptionPane.INFORMATION_MESSAGE, null,
										    possibleValues, possibleValues[0]);
					//					jdialog.show();
					if (selectedValue != null)
					    newString = selectedValue.toString();
					else{
					    newString = "";
					    fehler = true;
					}
				    }
				    else
					newString = v.elementAt(0).toString();
				  
				} else{
				    //				    IdeMessageManagerAccess.printMessage(IdeMessageType.ERROR_MODAL,"Selected method has no parameter");
				    // muss jetzt constraint abbrechen!!!!!
				    fehler = true;
				}
			    }

			    
			}

		    
			//------------------------------------------------------
			
			
			if ((!fehler) && (newString==null))
			    newString = getStringPropertyValue(mappingVector.elementAt(j+2).toString());
			
			start = 0;
			if (! fehler) {
			    while (start >= 0 ) {
				start = stringBuffer.toString().indexOf( mappingVector.elementAt(j+1).toString(),start);
				//				System.out.println("index von "+mappingVector.elementAt(j+1).toString()+" in "+stringBuffer.toString()+" ist "+start+"\n");
				length = mappingVector.elementAt(j+1).toString().length();
				if (start != -1) { 
				    
				    //  System.out.println(newString+"\n");
				    if (newString == null) 
					newString="";
				    if (start >= 0)
					stringBuffer.replace(start, start+length, newString );
				    start += newString.length();
				}
			    }
			}
		    }
		}
	    
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"angepa�tes Constraint: "+stringBuffer.toString());		               
		// are there OCL-Constraints for this method?
		String whichMethod = "";
		if (! fehler){
		    for (int k=0; k<placeVector.size(); k += 6){
			//found
			//			System.out.println("placeVector: "+placeVector.elementAt(k).toString()+"\n");
			//			System.out.println("constrintVecotr: "+constraintVector.elementAt(i).toString()+"\n");
			
			if  (placeVector.elementAt(k).toString().equals(constraintVector.elementAt(i).toString())) {
			    
			    //			    System.out.println("SECHS\n");
			    if ( "class".equals ( placeVector.elementAt ( k+2 ) .toString () ) ) {
				//System.out.println("SIEBEN\n");
				for (int j=0; j<mappingVector.size(); j=j+3){
				    if ( mappingVector.elementAt ( j ).toString ().equals
					 ( placeVector.elementAt ( k ).toString () )  &&
					 mappingVector.elementAt ( j+1 ).toString().
					 equals(placeVector.elementAt ( k+3 ).toString()) && 
					 (placeVector.elementAt ( k+5 ).toString ().equals
					  ( constraintVector.elementAt ( i+2 ).toString() ) ) ) {
					
					//System.out.println("ACHT\n");
					if (getStringPropertyValue(mappingVector.elementAt(j+2).toString()) != null){
					    //System.out.println("NEUN\n");
					    SciClass searchedClass = findClassByName(getStringPropertyValue(mappingVector.elementAt(j+2).toString()));
					    if (searchedClass != null) {
						String old=searchedClass.getTagList().getTagValue("invariants");
						//						System.out.println("ZZZZZZZZZZZZZZZZZZZZZZ "+stringBuffer.toString());
						if (old==null) {
						    searchedClass.getTagList().setTagValue("invariants",stringBuffer.toString());
						} else {
						    searchedClass.getTagList().setTagValue("invariants",old+" \nand "+stringBuffer.toString());
						}
					    }
					}
					//					IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Dieses Constraint soll zu: "+placeVector.elementAt(k+3).toString()+ " : "+getStringPropertyValue(mappingVector.elementAt(j+2).toString()) );
					
					
				    }
				}
			    }
			    
			    if ( "method".equals ( placeVector.elementAt ( k+2 ).toString () ) ) {
				for (int j=0; j<mappingVector.size(); j=j+3){
				    if ( mappingVector.elementAt(j).toString().equals
					 ( placeVector.elementAt(k).toString() ) &&
					 (mappingVector.elementAt(j+1).toString().equals
					  ( placeVector.elementAt(k+3).toString())) && 
					 (placeVector.elementAt(k+5).toString().equals
					  ( constraintVector.elementAt(i+2).toString())) ) {
					
					String className="";
					
					if ( "selectedMethod".equals ( mappingVector.elementAt(j+1).toString() ) ) {
					    //					    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Habs gefunden!!!\n" );
					    SciFunction member = getSelectedMethod();
					    SciFunction cpy = (SciFunction)member.copy();
					    if ("postcondition#".equals ( placeVector.elementAt(k+1).toString()) )
						cpy.getTagList().setTagValue("postconditions",stringBuffer.toString());
					    else
						if ("precondition#".equals ( placeVector.elementAt(k+1).toString()) )
						    cpy.getTagList().setTagValue("preconditions",stringBuffer.toString());
					    member.replace(cpy);
					} 
					else {				    
					    // find name of class this method belongs to
					    for (int z=0; z<mappingVector.size(); z+=3){
						if (mappingVector.elementAt(z).toString().equals(constraintVector.elementAt(i).toString())){
						    if (mappingVector.elementAt(z+1).toString().equals(placeVector.elementAt(k+4).toString())){
							
							if ( "selectedClass".equals ( mappingVector.elementAt(z+1).toString())) {
							    //							    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Habs gefunden!!!\n" );
							    if (getSelectedClass()!=null){
								s = getSelectedClass().toString();
								className = s.substring( s.indexOf("Class#")+6, s.indexOf(":",s.indexOf("Class#")));
							    }
							    else
								className = "";			       
							}
							else
							    className = getStringPropertyValue(mappingVector.elementAt(z+2).toString());
							
							
							//							IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Classname ist: "+ className +"\n" );
							
						    }
						}
					    }				    
					    
					    
					    if (findClassByName(className) != null){
						Enumeration allMembersEnum = SciUtil.allMembers(findClassByName(className),false);
						SciMember member;
						while (allMembersEnum.hasMoreElements()){
						    member = (SciMember)allMembersEnum.nextElement();
						    //						    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Alle Members: "+member.toString()+"\n");
						    if ( (member.toString().indexOf("#"+className+"#") != -1) && (member instanceof SciOperation) && (member.toString().indexOf(getStringPropertyValue(mappingVector.elementAt(j+2).toString())) != -1)) {
							
							//							IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Habs gefunden!!!\n" );
							SciMember cpy = (SciMember)member.copy();
							
							if ("postcondition#".equals ( placeVector.elementAt(k+1).toString()))
							    cpy.getTagList().setTagValue("postconditions",stringBuffer.toString());
							else
							    if ( "precondition#".equals ( placeVector.elementAt(k+1).toString() ) )
								cpy.getTagList().setTagValue("preconditions",stringBuffer.toString());
							
							
							member.replace(cpy);
						    }
						    
						}
					    }
					    
					    //					    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,"Dieses Constraint soll zu: "+placeVector.elementAt(k+3).toString()+ " : "+getStringPropertyValue(mappingVector.elementAt(j+2).toString().trim()) );
					}
				    }
				}
			    }
			}
		    }    
		}
	    }
	    
	}
	
    }
        
}
