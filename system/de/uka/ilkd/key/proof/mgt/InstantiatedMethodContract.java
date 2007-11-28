// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import java.util.Map;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.SymbolReplacer;

/**
 * @deprecated
 */
public class InstantiatedMethodContract {

    private Term pre;
    private Term post;
    private Term atPreAxioms;
    private Term ws;
    private SetOfLocationDescriptor modifies;
    private Modality modality;
    private ProgramVariable exc;
    private Namespace functions;
    private Namespace programVariables;
    private SymbolReplacer pvr;
    
    public static InstantiatedMethodContract create(Map m, Term pre, Term post, 
                                                    Term ws, Term atPreAxioms,                                                       
                                                    SetOfLocationDescriptor mods, 
                                                    Modality modality,
                                                    ProgramVariable exc,                                                   
                                                    Namespace functions,
                                                    Namespace programVariables) {
        assert modality != null; 
        
        final SymbolReplacer pvr = new SymbolReplacer(m);    
        return new InstantiatedMethodContract(replace(pvr, pre), 
                                              replace(pvr, post),
                                              ws!=null ? replace(pvr, ws) : null,
                                              replace(pvr, atPreAxioms),
                                              replace(pvr, mods),                                              
                                              modality, exc,                                               
                                              functions, programVariables, pvr);
    }
    
    /**
     * replaces the template locations in term <tt>t</tt> by the concrete ones 
     * contained in the instantiation map of pvr
     * @param pvr the SymbolReplacer
     * @param t the Term whose location templates are instantiated
     * @return the instantiated term <tt>t</tt>
     */
    private static Term replace(SymbolReplacer pvr, Term t) {
        return pvr.replace(t);
    }
    
    /**
     * used to replace the template locations used in LocationDescriptor by the one
     * in the replacement map of <tt>pvr</tt>
     * @param pvr the SymbolReplacer 
     * @param mods the SetOfLocationDescriptor to be instantiated
     * @return the instantiated set of location descriptors
     */
    private static SetOfLocationDescriptor replace(SymbolReplacer pvr, 
                                             SetOfLocationDescriptor mods) {
        SetOfLocationDescriptor result = SetAsListOfLocationDescriptor.EMPTY_SET;
        final IteratorOfLocationDescriptor it = mods.iterator();
        while ( it.hasNext() ) {
            result = result.add(pvr.replace(it.next()));
        }
        return result;
    }
    
    
    private InstantiatedMethodContract(Term pre, Term post, Term ws, 
                                       Term atPreAxioms,
                                       SetOfLocationDescriptor mods, 
                                       Modality modality, ProgramVariable exc,
                                       Namespace functions, Namespace programVariables,
                                       SymbolReplacer pvr) {
        this.pre = pre;
        this.atPreAxioms = atPreAxioms;
        this.ws = ws;
        this.post = post;
        this.modifies = mods;
        this.modality = modality;
        this.exc = exc;
        this.functions = functions;
        this.programVariables = programVariables;
        this.pvr = pvr;
    }
    
    public Term getPre() {
        return pre;
    }
    
    public Term getPost() {
        return post;
    }
    
    public Term getAtPreAxioms() {
        return atPreAxioms;
    }
    
    public SetOfLocationDescriptor getModifies() {
        return modifies;
    }
    
    public Modality getModality() {
        return modality;
    }    
    
    public ProgramVariable getExceptionVariable() {
        return exc;
    }
    
    public Term getWorkingSpace(){
        return ws;
    }
    
    public Namespace getAdditionalProgramVariables() {
        return programVariables;
    }
        
    public Namespace getAdditionalFunctions() {
        return functions;
    }
    
    public SymbolReplacer getProgramVariableReplacer(){
        return pvr;
    }
    
}
