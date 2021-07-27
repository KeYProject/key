package de.uka.ilkd.key.informationflow.po.snippet;

import java.lang.reflect.InvocationTargetException;
import java.util.EnumMap;
import java.util.logging.Level;
import java.util.logging.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopSpecification;


/**
 *
 * @author christoph
 */
class InfFlowPOSnippetFactoryImpl implements InfFlowPOSnippetFactory {

    /** Collection of data important for the production of snippets. */
    final BasicSnippetData data;

    /** The first copy of the proof obligation variables. */
    final ProofObligationVars poVars1;

    /** The second copy of the proof obligation variables. */
    final ProofObligationVars poVars2;


    /**
     * Registered snippet factory methods.
     */
    private final EnumMap<Snippet, InfFlowFactoryMethod> factoryMethods =
            new EnumMap<Snippet, InfFlowFactoryMethod>(Snippet.class);


    InfFlowPOSnippetFactoryImpl(InformationFlowContract contract,
                                ProofObligationVars vars1,
                                ProofObligationVars vars2,
                                Services services) {
        this.data = new BasicSnippetData(contract, services);
        this.poVars1 = vars1.labelHeapAtPreAsAnonHeapFunc();
        this.poVars2 = vars2.labelHeapAtPreAsAnonHeapFunc();
        registerFactoryMethods();
    }

    InfFlowPOSnippetFactoryImpl(BlockContract contract,
                                ProofObligationVars vars1,
                                ProofObligationVars vars2,
                                ExecutionContext context,
                                Services services) {
        this.data = new BasicSnippetData(contract, context, services);
        this.poVars1 = vars1.labelHeapAtPreAsAnonHeapFunc();
        this.poVars2 = vars2.labelHeapAtPreAsAnonHeapFunc();
        registerFactoryMethods();
    }

    InfFlowPOSnippetFactoryImpl(LoopSpecification invariant,
                                ProofObligationVars vars1,
                                ProofObligationVars vars2,
                                ExecutionContext context,
                                Term guardTerm,
                                Services services) {
        this.data = new BasicSnippetData(invariant, context, guardTerm, services);
        this.poVars1 = vars1.labelHeapAtPreAsAnonHeapFunc();
        this.poVars2 = vars2.labelHeapAtPreAsAnonHeapFunc();
        registerFactoryMethods();
    }

    InfFlowPOSnippetFactoryImpl(BasicSnippetData d,
                                ProofObligationVars vars1,
                                ProofObligationVars vars2) {
        this.data = d;
        this.poVars1 = vars1.labelHeapAtPreAsAnonHeapFunc();
        this.poVars2 = vars2.labelHeapAtPreAsAnonHeapFunc();
        registerFactoryMethods();
    }


    private void registerFactoryMethods() {
        try {
            for (Snippet s : Snippet.values()) {
                InfFlowFactoryMethod fm =
                        (InfFlowFactoryMethod) s.c.getDeclaredConstructor().newInstance();
                factoryMethods.put(s, fm);
            }
        } catch (InstantiationException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (IllegalArgumentException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (InvocationTargetException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (NoSuchMethodException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        } catch (SecurityException ex) {
            Logger.getLogger(InfFlowPOSnippetFactoryImpl.class.getName()).
                    log(Level.SEVERE, null, ex);
        }
    }


    @Override
    public Term create(Snippet snippet) throws UnsupportedOperationException {
        try {
            InfFlowFactoryMethod m = factoryMethods.get(snippet);
            if (m == null) {
                throw new UnsupportedOperationException("Unknown factory " +
                         "method for snippet \"" + snippet.name() + ".");
            }
            Term result = m.produce(data, poVars1, poVars2);
            return result;
        } catch (TermCreationException e) {
            throw new UnsupportedOperationException("Factory method for " +
                     "snippet \"" + snippet.name() + "threw " +
                     "TermCreationException: " + e.getMessage());
        }
    }
}