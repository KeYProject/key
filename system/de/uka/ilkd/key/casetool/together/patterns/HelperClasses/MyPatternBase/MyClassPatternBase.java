// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyPatternBase;

import com.togethersoft.openapi.sci.SciClass;
import com.togethersoft.openapi.sci.pattern.SciPatternProperty;


public class MyClassPatternBase extends MyPatternBase {

    public SciClass getSelectedClass() {
        Object selectedObject = getProperties().getPropertyValue(SciPatternProperty.ELEMENT);
        if (selectedObject != null && selectedObject instanceof SciClass) {
            return (SciClass)selectedObject;
        }
        else {
            return null;
        }
    }

}
