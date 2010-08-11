// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.java;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYProgModelInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MemoryAreaEC;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rtsj.proof.init.RTSJProfile;

public class RTSJInfo extends JavaInfo {

    private LocationVariable defaultMemoryArea;
    private LocationVariable immortalMemoryArea;

    {
	commonTypes = new KeYJavaType[6];
    }
    
    public RTSJInfo(KeYProgModelInfo kpmi, Services s) {
	super(kpmi, s);
    }

    public RTSJInfo(RTSJInfo rtsjInfo, Services serv) {
	super(rtsjInfo, serv);
    }

    /**
     * copies this JavaInfo and uses the given Services object as the
     * Services object of the copied JavaInfo
     * @param serv the Services the copy will use and vice versa
     * @return a copy of the JavaInfo
     */
    public RTSJInfo copy(Services serv) {
 	return new RTSJInfo(this, serv);
    }
    
    protected void fillCommonTypesCache() {
	if (commonTypesCacheValid) return;

	final String[] fullNames = new String[] { "java.lang.Object",
	        "java.lang.Cloneable", "java.io.Serializable",
	        "javax.realtime.MemoryArea", "javax.realtime.ScopedMemory",
	        "javax.realtime.ImmortalMemory" };
	
	for (int i = 0; i<fullNames.length; i++) {
	    commonTypes[i] = getKeYJavaTypeByClassName(fullNames[i]);            
	}
	commonTypesCacheValid = true;
    }

    /**
     * returns the KeYJavaType for class <tt>java.realtime.MemoryArea</tt>
     */
    public KeYJavaType getJavaxRealtimeMemoryArea() {
        assert ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile;
        
        if (commonTypes[3] == null) {
            commonTypes[3] = getKeYJavaTypeByClassName("javax.realtime.MemoryArea");
        }
        return commonTypes[3];
    }

    /**
     * returns the KeYJavaType for class <tt>java.realtime.ScopedMemory</tt>
     */
    public KeYJavaType getJavaxRealtimeScopedMemory() {
        assert ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile;
        if (commonTypes[4] == null) {
            commonTypes[4] = getKeYJavaTypeByClassName("javax.realtime.ScopedMemory");
        }
        return commonTypes[4];
    }

    /**
     * returns the KeYJavaType for class <tt>java.realtime.ImmortalMemory</tt>
     */
    public KeYJavaType getJavaxRealtimeImmortalMemory() {
        assert ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile;
        if (commonTypes[5] == null) {
            commonTypes[5] = getKeYJavaTypeByClassName("javax.realtime.ImmortalMemory");
        }
        return commonTypes[5];
    }

    public LocationVariable getDefaultMemoryArea() {
        if (!(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile)) {
            return null;
        }
        if(defaultMemoryArea==null){
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");                
            }
            defaultMemoryArea = (LocationVariable) services.getNamespaces().
                programVariables().lookup(new Name("initialMemoryArea"));
            KeYJavaType kjt = getTypeByClassName("javax.realtime.LTMemory");
            if(defaultMemoryArea == null){
                defaultMemoryArea = 
                    new LocationVariable(new ProgramElementName("initialMemoryArea"),
                            kjt);
                services.getNamespaces().programVariables().add(defaultMemoryArea);
            }
        }
        return defaultMemoryArea;
    }

    public LocationVariable getImmortalMemoryArea() {
        if (!(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile)) {
            return null;
        }
        if(immortalMemoryArea==null){
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");                
            }
            immortalMemoryArea = (LocationVariable) services.getNamespaces().
                programVariables().lookup(new Name("immortalMemoryArea"));
            KeYJavaType kjt = getTypeByClassName("javax.realtime.MemoryArea");
            if(immortalMemoryArea == null){
                immortalMemoryArea = 
                    new LocationVariable(new ProgramElementName("immortalMemoryArea"),
                            kjt);
                services.getNamespaces().programVariables().add(immortalMemoryArea);
            }
        }
        return immortalMemoryArea;
    }
    
    
    /**
     * returns the default execution context. This is equiavlent to executing the program
     * in a static method of a class placed in the default package 
     * @return the default execution context
     */
    public ExecutionContext getDefaultExecutionContext() {
        if (defaultExecutionContext == null) {                                   
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");                
            }
            final KeYJavaType kjt = 
                getKeYJavaTypeByClassName(DEFAULT_EXECUTION_CONTEXT_CLASS);                     
            final LocationVariable memArea = getDefaultMemoryArea();
            defaultExecutionContext = 
                new ExecutionContext(new TypeRef(kjt), memArea != null ? new MemoryAreaEC(memArea) : null, null);
        }
        return defaultExecutionContext;
    }
    

    
}
