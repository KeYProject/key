package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import java.util.EnumMap;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author christoph
 */
class SymbExecPOSnippetFactoryImpl extends BasicPOSnippetFactoryImpl
        implements SymbExecPOSnippetFactory {
    
    /**
     * JavaInfo belonging to the proof obligation.
     */
    private final JavaInfo javaInfo;
    
    /**
     * Registered snippet factory methods.
     */
    private final EnumMap<SymbExecPOSnippetFactory.Snippet, SymbExecFactoryMethod> factoryMethods
             = new EnumMap<SymbExecPOSnippetFactory.Snippet, SymbExecFactoryMethod>(SymbExecPOSnippetFactory.Snippet.class);


    SymbExecPOSnippetFactoryImpl(InformationFlowContract contract,
                                 JavaInfo javaInfo,
                                 ProofObligationVars vars,
                                 Services services) {
        super(contract, vars, services);
        this.javaInfo = javaInfo;
        
        // register FactoryMethods
        try {
            for (SymbExecPOSnippetFactory.Snippet s : SymbExecPOSnippetFactory.Snippet.values()) {
                SymbExecFactoryMethod fm = (SymbExecFactoryMethod)s.c.newInstance();
                factoryMethods.put(s, fm);
            }
        } catch (InstantiationException ex) {
            Logger.getLogger(SymbExecPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            Logger.getLogger(SymbExecPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        }
    }
    
    
    @Override
    public Term create(SymbExecPOSnippetFactory.Snippet snippet)
            throws UnsupportedOperationException {
        try {
            SymbExecFactoryMethod m = factoryMethods.get(snippet);
            if (m == null) {
                throw new UnsupportedOperationException("Unknown factory "
                        + "method for snippet \"" + snippet.name() + ".");
            }
            return m.produce(this, data, poVars, javaInfo);
        } catch (TermCreationException e) {
            throw new UnsupportedOperationException("Factory method for "
                    + "snippet \"" + snippet.name() + "threw "
                    + "TermCreationException: " + e.getMessage());
        }
    }

}
