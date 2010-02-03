// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.JAVA.CLASS.KeY_Idiom.InvariantConstraints; 
import java.util.Vector;

import com.togethersoft.modules.patterns.UNIVERSAL.PatternBaseException;
import com.togethersoft.modules.patterns.UNIVERSAL.PatternUIBuilder;

import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyPattern;

public class Pattern extends KeyPattern {

    private static final String PATTERN_NAME = "InvariantConstraints";

    public Pattern() {
        setPatternDisplayName(PATTERN_NAME);
    }

    protected void finalize1() throws Throwable {
	//        super.finalize();
	superFinalizeSimu();
        if (myUIBuilder != null) {
            myUIBuilder.removeAllListenedInspectorProperties();
            myUIBuilder = null;
        }
        myClassRoleVector.removeAllElements();
        myClassRoleVector = null;
    }

    public boolean prepare1() {
        try {
	    //            super.prepare();
	    superPrepareSimu();
            notImplementedForIDL();

            myClassRoleVector.removeAllElements();

	    // hack!!! if this is left out the combobox
	    // will not be initialized with any value!
	    setPropertyValue("lowerOperator",">");
	    setPropertyValue("upperOperator","<");

            initializeInspector();
            assignActivityResponse();

	    //----------------------------------------------------------------

	    initPattern();
 	    
	    //----------------------------------------------------------------

            return true;
        }
        catch(PatternBaseException e) {
            return false;
        }
    }

    public boolean canApply1() {
	return true;
      }

    public void apply1() {
        if (!canApply()) {
            return;
        }
	//        super.apply();
	superApplySimu();

        myClassRoleVector.removeAllElements();
        myUIBuilder.removeAllListenedInspectorProperties();
        myUIBuilder = null;

	//----------------------------------------------------------------
        applyOCLSchemes();
	//----------------------------------------------------------------
    }

    protected void initializeInspector() {
        try {
            myUIBuilder = null;
            myUIBuilder = createUIBuilder(true);

            Vector inspectorPropertiesVector = new Vector();

            // Create page
            String pageName1 = "Pattern properties";
            if (myUIBuilder.addInspectorPage(pageName1, PatternUIBuilder.UIPresentation.Table) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }

	    //----------------------------------------------------------------
	    setUIBuilder(myUIBuilder);
	    setPageName(pageName1);
	    //----------------------------------------------------------------

            myUIBuilder.setCreatedPatternUI();
            myUIBuilder.assignListenedInspectorProperties(inspectorPropertiesVector);

	    //---------------------------------------------------------------
	    addToPropertiesVector(inspectorPropertiesVector);
	    //---------------------------------------------------------------

        }
        catch (PatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }

    protected void assignActivityResponse() {
    }

    private PatternUIBuilder    myUIBuilder = null;
    private Vector              myClassRoleVector = new Vector();


}
