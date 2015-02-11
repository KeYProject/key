// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;


public abstract class SchemaVariableModifierSet {

    private boolean strict = false;
    private boolean rigid  = false;
    private boolean list = false;
    
    
    public boolean rigid() {
        return rigid;
    }
    
    
    protected boolean rigidEnabled() {
        return false;
    }
    
    
    public boolean strict() {
        return strict;
    }
    
    
    protected boolean strictEnabled() {
        return false;
    }
    

    public boolean list() {
	return list;
    }
    
    
    protected boolean listEnabled() {
	return false;
    }
    
    
    /**
     * @return <code>true</code> iff <code>option</code> is a valid modifier
     *         for the considered kind of schema variables
     */
    public boolean addModifier(String option) {
        if ( "strict".equals ( option ) ) {
            return addStrict ();
        } else if ( "rigid".equals ( option ) ) {
            return addRigid ();
        } else if ("list".equals(option)) {
            return addList();
        }

        return false;
    }
        
    public boolean addRigid() {
        this.rigid = true;
        return rigidEnabled();
    }
    public boolean addStrict() {
        this.strict = true;
        return strictEnabled();
    }
    public boolean addList() {
	this.list = true;
	return listEnabled();
    }

    public static class ProgramSV extends SchemaVariableModifierSet {
        protected boolean listEnabled() {
            return true;
        }
    }

    public static class TermSV extends SchemaVariableModifierSet {        
        protected boolean rigidEnabled() {
            return true;
        }
        protected boolean strictEnabled() {
            return true;
        }
        protected boolean listEnabled() {
            return true;
        }
    }

    public static class FormulaSV extends SchemaVariableModifierSet {
        protected boolean rigidEnabled() {
            return true;
        }
    }

    public static class VariableSV extends SchemaVariableModifierSet {}

    public static class SkolemTermSV extends SchemaVariableModifierSet {}

    public static class FreshProgVarSV extends SchemaVariableModifierSet {}

    public static class TermLabelSV extends SchemaVariableModifierSet {}
}