package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.Taclet;

public interface SMTSettings {

    public long       getTimeout();
    public String      getCommand(SolverType type);
    public String     getSMTTemporaryFolder();
    

    
    public int        getMaxConcurrentProcesses();
    
    public boolean   useExplicitTypeHierarchy();
    public boolean   instantiateNullAssumption();
    
    public boolean             makesUseOfTaclets();
    public int                  getMaxNumberOfGenerics();
    public Collection<Taclet>   getTaclets(Services services);
    

       
}
