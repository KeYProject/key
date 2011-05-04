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
}