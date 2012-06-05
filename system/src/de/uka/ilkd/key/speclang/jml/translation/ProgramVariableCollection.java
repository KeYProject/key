/**
 * 
 */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class ProgramVariableCollection {
    public ProgramVariable selfVar;
    public ImmutableList<ProgramVariable> paramVars;
    public ProgramVariable resultVar;
    public ProgramVariable excVar;
    public Map<LocationVariable,LocationVariable> atPreVars ;
    public Map<LocationVariable,Term> atPres;
    
    public ProgramVariableCollection(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable excVar,
            Map<LocationVariable,LocationVariable> atPreVars, Map<LocationVariable,Term> atPres) {
        super();
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.atPreVars = atPreVars;
        this.atPres = atPres;
    }

    public ProgramVariableCollection() {
    }
}
