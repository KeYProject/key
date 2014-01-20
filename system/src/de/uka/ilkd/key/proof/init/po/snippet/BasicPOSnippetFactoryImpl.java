package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopInvariant;

import java.util.EnumMap;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author christoph
 */
class BasicPOSnippetFactoryImpl implements BasicPOSnippetFactory {
    
    /**
     * Collection of data important for the production of snippets.
     */
    private final BasicSnippetData data;
    
    /**
     * Variables belonging to the proof obligation.
     */
    private final ProofObligationVars poVars;

    /**
     * Registered snippet factory methods.
     */
    private final EnumMap<Snippet, FactoryMethod> factoryMethods
             = new EnumMap<Snippet, FactoryMethod>(Snippet.class);


    BasicPOSnippetFactoryImpl(BasicSnippetData data, ProofObligationVars poVars) {
        this.data = data;
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(FunctionalOperationContract contract,
                              ProofObligationVars poVars,
                              Services services) {
        this.data = new BasicSnippetData(contract, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }
    
    BasicPOSnippetFactoryImpl(LoopInvariant invariant,
                              ProofObligationVars poVars,
                              ExecutionContext context,
                              Term guardTerm,
                              Services services) {
        this.data = new BasicSnippetData(invariant, context, guardTerm, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(InformationFlowContract contract,
                              ProofObligationVars poVars,
                              Services services) {
        this.data = new BasicSnippetData(contract, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(BlockContract contract,
                              ProofObligationVars poVars,
                              ExecutionContext context,
                              Services services) {
        this.data = new BasicSnippetData(contract, context, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    private void registerFactoryMethods() {
        try {
            for (Snippet s : Snippet.values()) {
                FactoryMethod fm = (FactoryMethod)s.c.newInstance();
                factoryMethods.put(s, fm);
            }
        } catch (InstantiationException ex) {
            Logger.getLogger(BasicPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            Logger.getLogger(BasicPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        }
    }


    @Override
    public Term create(Snippet snippet) throws UnsupportedOperationException {
        try {
            FactoryMethod m = factoryMethods.get(snippet);
            if (m == null) {
                throw new UnsupportedOperationException("Unknown factory "
                        + "method for snippet \"" + snippet.name() + ".");
            }
            return m.produce(data, poVars);
        } catch (TermCreationException e) {
            throw new UnsupportedOperationException("Factory method for "
                    + "snippet \"" + snippet.name() + " threw "
                    + "TermCreationException: " + e.getMessage());
        }
    }

}
