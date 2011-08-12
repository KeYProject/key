/**
 * 
 */
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class ProgramVariableCollection {
    public ProgramVariable selfVar;
    public ImmutableList<ProgramVariable> paramVars;
    public ProgramVariable resultVar;
    public ProgramVariable excVar;
    public LocationVariable heapAtPreVar ;
    public Term heapAtPre;
    
    public ProgramVariableCollection(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable excVar,
            LocationVariable heapAtPreVar, Term heapAtPre) {
        super();
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.heapAtPreVar = heapAtPreVar;
        this.heapAtPre = heapAtPre;
    }

    public ProgramVariableCollection() {
    }
}